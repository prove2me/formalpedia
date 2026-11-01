-- Prove2me | solution 1 for InconsistentDR.Shadow.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T00:13:45.753206+00:00
-- url     : https://prove2.me/submissions/cb4b560e-5443-4bdc-a47c-5f9b6f12be7b

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators
import Theorems.Thm_InconsistentDR_Shadow_lemma_3_2
import Theorems.Thm_InconsistentDR_Shadow_convex_closure_dom

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence

namespace DR33Aux

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma res_mem (A : X → Set X) (J : X → X) (hJ : IsResolvent 1 A J) (x : X) :
    x - J x ∈ A (J x) := by
  have := hJ x; rwa [inv_one, one_smul] at this

/-- `⟪J x - J y, J_{A⁻¹} x - J_{A⁻¹} y⟫ ≥ 0`. -/
lemma res_inner_nonneg (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X)
    (hJ : IsResolvent 1 A J) (x y : X) :
    0 ≤ ⟪J x - J y, (x - J x) - (y - J y)⟫_ℝ :=
  hA _ _ _ _ (res_mem A J hJ x) (res_mem A J hJ y)

lemma res_unique (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X) (hJ : IsResolvent 1 A J)
    {x y : X} (hy : x - y ∈ A y) : J x = y := by
  have := hA _ _ _ _ (res_mem A J hJ x) hy
  have e : (x - J x) - (x - y) = -(J x - y) := by abel
  rw [e, inner_neg_right, real_inner_self_eq_norm_sq] at this
  have h0 : ‖J x - y‖ = 0 := by nlinarith [norm_nonneg (J x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- The reflected resolvent is nonexpansive. -/
lemma refl_nonexp (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X) (hJ : IsResolvent 1 A J)
    (x y : X) : ‖InconsistentDR.Shadow.refl J x - InconsistentDR.Shadow.refl J y‖ ≤ ‖x - y‖ := by
  have h := res_inner_nonneg A hA J hJ x y
  have e : InconsistentDR.Shadow.refl J x - InconsistentDR.Shadow.refl J y =
      (J x - J y) - ((x - J x) - (y - J y)) := by
    simp only [InconsistentDR.Shadow.refl]; module
  have e2 : x - y = (J x - J y) + ((x - J x) - (y - J y)) := by abel
  have h2 : ‖InconsistentDR.Shadow.refl J x - InconsistentDR.Shadow.refl J y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 := by
    rw [e, e2, norm_sub_sq_real, norm_add_sq_real]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The Douglas–Rachford operator is firmly nonexpansive. -/
lemma drT_fne (A B : X → Set X) (hA : IsMonotoneOp A) (hB : IsMonotoneOp B) (JA JB : X → X)
    (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB) (x y : X) :
    ‖InconsistentDR.Shadow.drT JA JB x - InconsistentDR.Shadow.drT JA JB y‖ ^ 2 +
      ‖(x - InconsistentDR.Shadow.drT JA JB x) - (y - InconsistentDR.Shadow.drT JA JB y)‖ ^ 2
      ≤ ‖x - y‖ ^ 2 := by
  open InconsistentDR.Shadow in
  have hN : ‖refl JB (refl JA x) - refl JB (refl JA y)‖ ≤ ‖x - y‖ :=
    (refl_nonexp B hB JB hJB _ _).trans (refl_nonexp A hA JA hJA x y)
  open InconsistentDR.Shadow in
  have e1 : drT JA JB x - drT JA JB y =
      (1 / 2 : ℝ) • ((x - y) + (refl JB (refl JA x) - refl JB (refl JA y))) := by
    simp only [InconsistentDR.Shadow.drT, InconsistentDR.Shadow.refl]; module
  open InconsistentDR.Shadow in
  have e2 : (x - drT JA JB x) - (y - drT JA JB y) =
      (1 / 2 : ℝ) • ((x - y) - (refl JB (refl JA x) - refl JB (refl JA y))) := by
    simp only [InconsistentDR.Shadow.drT, InconsistentDR.Shadow.refl]; module
  rw [e1, e2]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hN 2
  generalize x - y = a at h2 ⊢
  generalize InconsistentDR.Shadow.refl JB (InconsistentDR.Shadow.refl JA x) -
    InconsistentDR.Shadow.refl JB (InconsistentDR.Shadow.refl JA y) = b at h2 ⊢
  rw [norm_smul, norm_smul, mul_pow, mul_pow, norm_add_sq_real, norm_sub_sq_real]
  have : ‖(1 / 2 : ℝ)‖ ^ 2 = 1 / 4 := by norm_num
  rw [this]
  nlinarith

/-- `Fix(v + T)` is invariant under `T` ([13, Proposition 2.5]). -/
lemma fix_step (T : X → X)
    (hfne : ∀ x y, ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2)
    (v : X) (hv : ∀ w, ‖v‖ ≤ ‖w - T w‖) (q : X) (hq : v + T q = q) :
    v + T (q - v) = q - v := by
  have hTq : T q = q - v := eq_sub_of_add_eq' hq
  have h := hfne q (q - v)
  rw [hTq, sub_sub_cancel] at h
  set w := q - v - T (q - v) with hw
  have hvw := hv (q - v)
  rw [← hw] at hvw
  have h2 : ‖v‖ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvw 2
  have h3 : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  have h5 : q - v - T (q - v) = v := (sub_eq_zero.mp (norm_eq_zero.mp h3)).symm
  calc v + T (q - v) = v + (q - v - (q - v - T (q - v))) := by abel
    _ = q - v := by rw [h5]; abel

/-- Uniqueness of the least-norm point of a convex set. -/
lemma minnorm_unique {C : Set X} (hC : Convex ℝ C) {v w : X}
    (hv : InconsistentDR.Shadow.IsMinNormPt C v) (hw : w ∈ C) (hle : ‖w‖ ≤ ‖v‖) : w = v := by
  have hmid : (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w ∈ C :=
    hC hv.1 hw (by norm_num) (by norm_num) (by norm_num)
  have h1 := hv.2 _ hmid
  have h2 : ‖v‖ ^ 2 ≤ ‖(1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w‖ ^ 2 := by gcongr
  have hpar : ‖(1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w‖ ^ 2 =
      (‖v‖ ^ 2 + ‖w‖ ^ 2) / 2 - ‖v - w‖ ^ 2 / 4 := by
    rw [← smul_add, norm_smul, mul_pow, norm_sub_sq_real, norm_add_sq_real]
    norm_num; ring
  have h3 : ‖w‖ ^ 2 ≤ ‖v‖ ^ 2 := by gcongr
  have h4 : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp h4)).symm

/-- Variational inequality for the least-norm point of a convex set. -/
lemma minnorm_vi {C : Set X} (hC : Convex ℝ C) {v : X} (hv : InconsistentDR.Shadow.IsMinNormPt C v)
    {d : X} (hd : d ∈ C) : 0 ≤ ⟪v, d - v⟫_ℝ := by
  by_contra hneg
  push Not at hneg
  set a := ⟪v, d - v⟫_ℝ
  set b := ‖d - v‖ ^ 2
  have hb : 0 ≤ b := by positivity
  set t := min 1 (-a / (b + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htb : t * (b + 1) ≤ -a := by
    have : t ≤ -a / (b + 1) := min_le_right _ _
    rwa [le_div_iff₀ (by linarith)] at this
  have hmem : v + t • (d - v) ∈ C := by
    have : v + t • (d - v) = (1 - t) • v + t • d := by module
    rw [this]; exact hC hv.1 hd (by linarith) ht0.le (by ring)
  have h1 := hv.2 _ hmem
  have h2 : ‖v‖ ^ 2 ≤ ‖v + t • (d - v)‖ ^ 2 := by gcongr
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht0.le] at h2
  have : t * (2 * a + t * b) < 0 := by
    apply mul_neg_of_pos_of_neg ht0
    nlinarith
  nlinarith

/-- The inverse operator `A⁻¹`. -/
def opInv (A : X → Set X) : X → Set X := fun u => {x | u ∈ A x}

lemma opInv_mono (A : X → Set X) (hA : IsMonotoneOp A) : IsMonotoneOp (opInv A) := by
  intro x y u w hu hw
  have := hA _ _ _ _ hu hw
  rwa [real_inner_comm] at this

lemma opInv_res (A : X → Set X) (J : X → X) (hJ : IsResolvent 1 A J) :
    IsResolvent 1 (opInv A) (fun x => x - J x) := by
  intro x
  rw [inv_one, one_smul]
  show x - J x ∈ A (x - (x - J x))
  rw [sub_sub_cancel]
  exact res_mem A J hJ x

/-- `cl D` and `cl R` are convex. -/
lemma convex_closure_D [CompleteSpace X] (A B : X → Set X) (hA : IsMonotoneOp A)
    (hB : IsMonotoneOp B) (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB) :
    Convex ℝ (closure (InconsistentDR.Shadow.setD A B)) := by
  have h1 := InconsistentDR.Shadow.convex_closure_dom A hA JA hJA
  have h2 := InconsistentDR.Shadow.convex_closure_dom B hB JB hJB
  have hsub : closure (InconsistentDR.Shadow.setD A B) = closure (closure (dom A) - closure (dom B)) := by
    apply le_antisymm
    · exact closure_mono (Set.sub_subset_sub subset_closure subset_closure)
    · apply closure_minimal _ isClosed_closure
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact map_mem_closure₂ continuous_sub ha hb (fun x hx y hy => ⟨x, hx, y, hy, rfl⟩)
  rw [hsub]
  exact (h1.sub h2).closure

lemma convex_closure_R [CompleteSpace X] (A B : X → Set X) (hA : IsMonotoneOp A)
    (hB : IsMonotoneOp B) (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB) :
    Convex ℝ (closure (InconsistentDR.Shadow.setR A B)) := by
  have h1 := InconsistentDR.Shadow.convex_closure_dom (opInv A) (opInv_mono A hA) _
    (opInv_res A JA hJA)
  have h2 := InconsistentDR.Shadow.convex_closure_dom (opInv B) (opInv_mono B hB) _
    (opInv_res B JB hJB)
  have eA : InconsistentDR.Shadow.ran A = dom (opInv A) := Set.ext fun u => Iff.rfl
  have eB : InconsistentDR.Shadow.ran B = dom (opInv B) := Set.ext fun u => Iff.rfl
  have hsub : closure (InconsistentDR.Shadow.setR A B) =
      closure (closure (dom (opInv A)) + closure (dom (opInv B))) := by
    unfold InconsistentDR.Shadow.setR
    rw [eA, eB]
    apply le_antisymm
    · exact closure_mono (Set.add_subset_add subset_closure subset_closure)
    · apply closure_minimal _ isClosed_closure
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact map_mem_closure₂ continuous_add ha hb (fun x hx y hy => ⟨x, hx, y, hy, rfl⟩)
  rw [hsub]
  exact (h1.add h2).closure

/-- Membership by maximality. -/
lemma maxmono_mem (A : X → Set X) (hA : IsMaximalMonotone A) (x u : X)
    (h : ∀ a a', a' ∈ A a → 0 ≤ ⟪x - a, u - a'⟫_ℝ) : u ∈ A x := by
  classical
  let A' : X → Set X := fun y => A y ∪ {w | y = x ∧ w = u}
  have hmono : IsMonotoneOp A' := by
    intro y1 y2 w1 w2 hw1 hw2
    rcases hw1 with hw1 | ⟨rfl, rfl⟩ <;> rcases hw2 with hw2 | ⟨rfl, rfl⟩
    · exact hA.1 _ _ _ _ hw1 hw2
    · have := h _ _ hw1
      rw [← neg_sub y2 y1, ← neg_sub w2 w1, inner_neg_neg]; exact this
    · exact h _ _ hw2
    · simp
  have heq := hA.2 A' hmono (fun y => Set.subset_union_left)
  have : u ∈ A' x := Or.inr ⟨rfl, rfl⟩
  rwa [heq] at this

lemma nonneg_of_affine {α β : ℝ} (h : ∀ t : ℝ, 0 ≤ t → 0 ≤ α + t * β) : 0 ≤ β := by
  by_contra hb
  push Not at hb
  have := h ((|α| + 1) / (-β)) (div_nonneg (by positivity) (by linarith))
  have hb0 : β ≠ 0 := hb.ne
  have e : (|α| + 1) / (-β) * β = -(|α| + 1) := by field_simp
  rw [e] at this
  linarith [le_abs_self α]


end DR33Aux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB) :
    ⟪vD, vR⟫_ℝ = 0 ∧ v = vD + vR ∧ ‖v‖ ^ 2 = ‖vD‖ ^ 2 + ‖vR‖ ^ 2 := by
  have hcD := DR33Aux.convex_closure_D A B hA.1 hB.1 JA JB hJA hJB
  have hcR := DR33Aux.convex_closure_R A B hA.1 hB.1 JA JB hJA hJB
  obtain ⟨L1A, L2A⟩ := lemma_3_2 A hA JA hJA
  obtain ⟨L1B, L2B⟩ := lemma_3_2 B hB JB hJB
  have viD : ∀ x ∈ closure (setD A B), 0 ≤ ⟪vD, x - vD⟫_ℝ :=
    fun x hx => DR33Aux.minnorm_vi hcD hvD hx
  have viR : ∀ x ∈ closure (setR A B), 0 ≤ ⟪vR, x - vR⟫_ℝ :=
    fun x hx => DR33Aux.minnorm_vi hcR hvR hx
  -- `cl dom A - cl dom B ⊆ cl D`, `cl ran A + cl ran B ⊆ cl R`
  have hsubD : ∀ a ∈ closure (dom A), ∀ b ∈ closure (dom B), a - b ∈ closure (setD A B) :=
    fun a ha b hb => map_mem_closure₂ continuous_sub ha hb (fun x hx y hy => ⟨x, hx, y, hy, rfl⟩)
  have hsubR : ∀ a ∈ closure (ran A), ∀ b ∈ closure (ran B), a + b ∈ closure (setR A B) :=
    fun a ha b hb => map_mem_closure₂ continuous_add ha hb (fun x hx y hy => ⟨x, hx, y, hy, rfl⟩)
  obtain ⟨a0, ha0⟩ : (dom A).Nonempty := ⟨JA 0, _, DR33Aux.res_mem A JA hJA 0⟩
  obtain ⟨b0, hb0⟩ : (dom B).Nonempty := ⟨JB 0, _, DR33Aux.res_mem B JB hJB 0⟩
  have ha0' : a0 ∈ closure (dom A) := subset_closure ha0
  have hb0' : b0 ∈ closure (dom B) := subset_closure hb0
  obtain ⟨r0, hr0⟩ : (ran A).Nonempty := ⟨_, JA 0, DR33Aux.res_mem A JA hJA 0⟩
  obtain ⟨s0, hs0⟩ : (ran B).Nonempty := ⟨_, JB 0, DR33Aux.res_mem B JB hJB 0⟩
  have hr0' : r0 ∈ closure (ran A) := subset_closure hr0
  have hs0' : s0 ∈ closure (ran B) := subset_closure hs0
  -- Fact 3.1-type locations
  have F1 : ∀ d, (∀ c ∈ closure (dom A), ∀ t : ℝ, 0 ≤ t → c + t • d ∈ closure (dom A)) →
      ⟪d, -vD⟫_ℝ ≤ 0 := by
    intro d hd
    have : 0 ≤ ⟪vD, d⟫_ℝ := by
      apply DR33Aux.nonneg_of_affine (α := ⟪vD, a0 - b0 - vD⟫_ℝ)
      intro t ht
      have := viD _ (hsubD _ (hd a0 ha0' t ht) b0 hb0')
      have e : a0 + t • d - b0 - vD = (a0 - b0 - vD) + t • d := by abel
      rwa [e, inner_add_right, real_inner_smul_right] at this
    rw [inner_neg_right, real_inner_comm]; linarith
  have F2 : ∀ d, (∀ c ∈ closure (dom B), ∀ t : ℝ, 0 ≤ t → c + t • d ∈ closure (dom B)) →
      ⟪d, vD⟫_ℝ ≤ 0 := by
    intro d hd
    have : 0 ≤ ⟪vD, -d⟫_ℝ := by
      apply DR33Aux.nonneg_of_affine (α := ⟪vD, a0 - b0 - vD⟫_ℝ)
      intro t ht
      have := viD _ (hsubD a0 ha0' _ (hd b0 hb0' t ht))
      have e : a0 - (b0 + t • d) - vD = (a0 - b0 - vD) + t • (-d) := by
        rw [smul_neg]; abel
      rwa [e, inner_add_right, real_inner_smul_right] at this
    rw [inner_neg_right, real_inner_comm] at this; linarith
  have F3 : ∀ d, (∀ c ∈ closure (ran A), ∀ t : ℝ, 0 ≤ t → c + t • d ∈ closure (ran A)) →
      ⟪d, -vR⟫_ℝ ≤ 0 := by
    intro d hd
    have : 0 ≤ ⟪vR, d⟫_ℝ := by
      apply DR33Aux.nonneg_of_affine (α := ⟪vR, r0 + s0 - vR⟫_ℝ)
      intro t ht
      have := viR _ (hsubR _ (hd r0 hr0' t ht) s0 hs0')
      have e : r0 + t • d + s0 - vR = (r0 + s0 - vR) + t • d := by abel
      rwa [e, inner_add_right, real_inner_smul_right] at this
    rw [inner_neg_right, real_inner_comm]; linarith
  have F4 : ∀ d, (∀ c ∈ closure (ran B), ∀ t : ℝ, 0 ≤ t → c + t • d ∈ closure (ran B)) →
      ⟪d, -vR⟫_ℝ ≤ 0 := by
    intro d hd
    have : 0 ≤ ⟪vR, d⟫_ℝ := by
      apply DR33Aux.nonneg_of_affine (α := ⟪vR, r0 + s0 - vR⟫_ℝ)
      intro t ht
      have := viR _ (hsubR r0 hr0' _ (hd s0 hs0' t ht))
      have e : r0 + (s0 + t • d) - vR = (r0 + s0 - vR) + t • d := by abel
      rwa [e, inner_add_right, real_inner_smul_right] at this
    rw [inner_neg_right, real_inner_comm]; linarith
  -- Proposition 3.3 (ii), (iv)
  have recA : ∀ c ∈ closure (dom A), ∀ t : ℝ, 0 ≤ t → c + t • (-vR) ∈ closure (dom A) :=
    L2A (-vR) F3
  have recB : ∀ c ∈ closure (dom B), ∀ t : ℝ, 0 ≤ t → c + t • (-vR) ∈ closure (dom B) :=
    L2B (-vR) F4
  have recRB : ∀ c ∈ closure (ran B), ∀ t : ℝ, 0 ≤ t → c + t • vD ∈ closure (ran B) :=
    L1B vD F2
  -- (v)
  have hv1 : ⟪-vR, -vD⟫_ℝ ≤ 0 := F1 (-vR) recA
  have hv2 : ⟪vD, -vR⟫_ℝ ≤ 0 := F4 vD recRB
  rw [inner_neg_neg] at hv1
  rw [inner_neg_right] at hv2
  have h5 : ⟪vD, vR⟫_ℝ = 0 := by rw [real_inner_comm] at hv1; linarith
  -- (vi)
  have h6D : vD + vR ∈ closure (setD A B) := by
    have := map_mem_closure (f := fun z => z + vR) (t := closure (setD A B)) (by fun_prop) hvD.1
      (by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hb' : b + (1 : ℝ) • (-vR) ∈ closure (dom B) := recB b (subset_closure hb) 1 zero_le_one
        have := hsubD a (subset_closure ha) _ hb'
        simp only [one_smul] at this
        show a - b + vR ∈ closure (setD A B)
        have e : a - b + vR = a - (b + -vR) := by abel
        rw [e]; exact this)
    rwa [closure_closure] at this
  have h6R : vD + vR ∈ closure (setR A B) := by
    have := map_mem_closure (f := fun z => z + vD) (t := closure (setR A B)) (by fun_prop) hvR.1
      (by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hb' : b + (1 : ℝ) • vD ∈ closure (ran B) := recRB b (subset_closure hb) 1 zero_le_one
        have := hsubR a (subset_closure ha) _ hb'
        simp only [one_smul] at this
        show a + b + vD ∈ closure (setR A B)
        have e : a + b + vD = a + (b + vD) := by abel
        rw [e]; exact this)
    rw [closure_closure] at this
    rwa [add_comm vD vR]
  -- (vii)
  have hset : closure (Set.range fun x => x - drT JA JB x) =
      closure (setD A B) ∩ closure (setR A B) := h12.1.trans h12.2
  rw [hset] at hv
  have hw : ‖v‖ ≤ ‖vD + vR‖ := hv.2 _ ⟨h6D, h6R⟩
  have i1 := viD v hv.1.1
  have i2 := viR v hv.1.2
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at i1 i2
  have hsq : ‖vD + vR‖ ^ 2 = ‖vD‖ ^ 2 + ‖vR‖ ^ 2 := by rw [norm_add_sq_real, h5]; ring
  have hle : ‖vD + vR‖ ^ 2 ≤ ⟪vD + vR, v⟫_ℝ := by
    rw [hsq, inner_add_left]; linarith
  have hcs : ⟪vD + vR, v⟫_ℝ ≤ ‖vD + vR‖ * ‖v‖ := real_inner_le_norm _ _
  have hw2 : ‖vD + vR‖ ≤ ‖v‖ := by
    by_cases h0 : ‖vD + vR‖ = 0
    · rw [h0]; exact norm_nonneg _
    · have hpos : 0 < ‖vD + vR‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  have h7 : vD + vR = v := DR33Aux.minnorm_unique (hcD.inter hcR) hv ⟨h6D, h6R⟩ hw2
  refine ⟨h5, h7.symm, ?_⟩
  rw [← h7, hsq]
