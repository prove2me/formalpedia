-- Prove2me | solution 1 for InconsistentDR.Shadow.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T00:01:30.833798+00:00
-- url     : https://prove2.me/submissions/6541a0a6-bed6-4e31-ac46-2a757688b43e

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators
import Theorems.Thm_InconsistentDR_Shadow_proposition_3_3
import Theorems.Thm_InconsistentDR_Shadow_proposition_4_2
import Theorems.Thm_InconsistentDR_Shadow_convex_closure_dom

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence

namespace DR43Aux

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

end DR43Aux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB) :
    {x | ∃ a ∈ A x, ∃ b ∈ B (x - vD), -vR + a + b = 0} ⊆ solZ A B v ∧
    (vR = 0 → {x | ∃ a ∈ A x, ∃ b ∈ B (x - vD), -vR + a + b = 0} = solZ A B v) := by
  obtain ⟨hDR, hvv, -⟩ := proposition_3_3 A B hA hB JA JB hJA hJB v vD vR hv hvD hvR h12
  have hcD := DR43Aux.convex_closure_D A B hA.1 hB.1 JA JB hJA hJB
  have hcR := DR43Aux.convex_closure_R A B hA.1 hB.1 JA JB hJA hJB
  have incl : {x | ∃ a ∈ A x, ∃ b ∈ B (x - vD), -vR + a + b = 0} ⊆ solZ A B v := by
    rintro x ⟨a, ha, b, hb, hab⟩
    have hb' : b = vR - a := by
      have : b = -(-vR + a) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hab
      rw [this]; abel
    -- (51): `v - a ∈ B (x - v)`
    have hmem : v - a ∈ B (x - v) := by
      apply DR43Aux.maxmono_mem B hB
      intro b0 b0' hb0
      have m := hB.1 _ _ _ _ hb hb0
      have hd := DR43Aux.minnorm_vi hcD hvD (subset_closure ⟨x, ⟨a, ha⟩, b0, ⟨b0', hb0⟩, rfl⟩)
      have hr := DR43Aux.minnorm_vi hcR hvR
        (subset_closure ⟨a, ⟨x, ha⟩, b0', ⟨b0, hb0⟩, rfl⟩)
      have e : ⟪x - v - b0, v - a - b0'⟫_ℝ = ⟪x - vD - b0, b - b0'⟫_ℝ + ⟪vD, x - b0 - vD⟫_ℝ +
          ⟪vR, a + b0' - vR⟫_ℝ - ⟪vD, vR⟫_ℝ := by
        rw [hvv, hb']
        simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right]
        rw [real_inner_comm vD vR, real_inner_comm vD x, real_inner_comm vD b0]
        ring
      rw [e, hDR]
      linarith
    exact ⟨a, ha, v - a, hmem, by abel⟩
  refine ⟨incl, fun hR0 => le_antisymm incl ?_⟩
  -- (ii)
  rintro x ⟨a, ha, b, hb, hab⟩
  have hvD' : v = vD := by rw [hvv, hR0, add_zero]
  have h1 : v - b ∈ A x := by
    have : v - b = a := by
      have : b = -(-v + a) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hab
      rw [this]; abel
    rw [this]; exact ha
  obtain ⟨-, -, ⟨h3, -⟩⟩ := proposition_4_2 A B hA hB JA JB hJA hJB v vD vR hv hvD hvR h12 1 0
    zero_le_one le_rfl x b h1 hb
  refine ⟨v - (1 : ℝ) • vD - b, h3, b, by rw [← hvD']; exact hb, ?_⟩
  rw [hR0, one_smul, hvD']; abel
