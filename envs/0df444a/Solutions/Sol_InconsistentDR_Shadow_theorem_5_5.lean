-- Prove2me | solution 1 for InconsistentDR.Shadow.theorem_5_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:56:17.282954+00:00
-- url     : https://prove2.me/submissions/1c9b0c4e-b4bf-4fb0-ab63-bdb2b543d09c

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators
import Theorems.Thm_InconsistentDR_Shadow_proposition_5_3

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence

namespace DR55Aux

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


/-- [14, Theorem 2.7(v)], display (65). -/
lemma ineq65 (A B : X → Set X) (hA : IsMonotoneOp A) (hB : IsMonotoneOp B) (JA JB : X → X)
    (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB) (u w : X) :
    ‖JA (InconsistentDR.Shadow.drT JA JB u) - JA (InconsistentDR.Shadow.drT JA JB w)‖ ^ 2 +
      ‖InconsistentDR.Shadow.resInv JA (InconsistentDR.Shadow.drT JA JB u) -
        InconsistentDR.Shadow.resInv JA (InconsistentDR.Shadow.drT JA JB w)‖ ^ 2 ≤
    ‖JA u - JA w‖ ^ 2 + ‖InconsistentDR.Shadow.resInv JA u - InconsistentDR.Shadow.resInv JA w‖ ^ 2 := by
  open InconsistentDR.Shadow in
  set Tu := drT JA JB u
  set Tw := drT JA JB w
  have hc := res_inner_nonneg A hA JA hJA Tu Tw
  have hb := res_inner_nonneg B hB JB hJB (refl JA u) (refl JA w)
  set a := JA u - JA w with ha
  set a' := resInv JA u - resInv JA w with ha'
  set b := JB (refl JA u) - JB (refl JA w) with hbdef
  set c := JA Tu - JA Tw with hcdef
  have eT : Tu - Tw = a' + b := by
    simp only [Tu, Tw, drT, ha', hbdef, resInv]; abel
  have eb' : (refl JA u - JB (refl JA u)) - (refl JA w - JB (refl JA w)) = (a - a') - b := by
    simp only [ha, ha', hbdef, resInv, InconsistentDR.Shadow.refl]; module
  have ec' : (Tu - JA Tu) - (Tw - JA Tw) = (a' + b) - c := by
    rw [← eT, hcdef]; abel
  rw [eb'] at hb
  rw [ec'] at hc
  have e1 : resInv JA Tu - resInv JA Tw = (a' + b) - c := by simp only [resInv]; exact ec'
  rw [e1]
  have h1 : ‖c‖ ^ 2 + ‖(a' + b) - c‖ ^ 2 ≤ ‖a' + b‖ ^ 2 := by
    have : a' + b = c + ((a' + b) - c) := by abel
    conv_rhs => rw [this]
    rw [norm_add_sq_real]
    linarith
  have h2 : ‖a' + b‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖a'‖ ^ 2 := by
    rw [norm_add_sq_real]
    have h3 : 0 ≤ ‖a - b‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real] at h3
    rw [inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq] at hb
    have : ⟪b, a⟫_ℝ = ⟪a, b⟫_ℝ := real_inner_comm _ _
    have : ⟪b, a'⟫_ℝ = ⟪a', b⟫_ℝ := real_inner_comm _ _
    linarith
  linarith


end DR55Aux

open InconsistentDR.Shadow in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB)
    (hfix : (FixSet fun y => v + drT JA JB y).Nonempty) (x : X) :
    (Bornology.IsBounded (Set.range fun n : ℕ => JA ((drT JA JB)^[n] x) + (n : ℝ) • vR) ∧
      Bornology.IsBounded
        (Set.range fun n : ℕ => resInv JA ((drT JA JB)^[n] x) + (n : ℝ) • vD)) ∧
    (IsParamonotone A → IsParamonotone B →
      IsFejerPair (fun n => JA ((drT JA JB)^[n] x) + (n : ℝ) • vR)
        (fun n => -v + (resInv JA ((drT JA JB)^[n] x) + (n : ℝ) • vD))
        (solZ A B v ×ˢ solK A B v)) := by
  set T := drT JA JB with hT
  have h65 := DR55Aux.ineq65 A B hA.1 hB.1 JA JB hJA hJB
  -- the Fejér distances along two orbits decrease
  have hdec : ∀ u w : X, ∀ n : ℕ,
      ‖JA (T^[n] u) - JA (T^[n] w)‖ ^ 2 + ‖resInv JA (T^[n] u) - resInv JA (T^[n] w)‖ ^ 2 ≤
        ‖u - w‖ ^ 2 := by
    intro u w n
    induction n with
    | zero =>
      simp only [Function.iterate_zero, id]
      have h := DR55Aux.res_inner_nonneg A hA.1 JA hJA u w
      have e : u - w = (JA u - JA w) + (resInv JA u - resInv JA w) := by
        simp only [resInv]; abel
      rw [e, norm_add_sq_real]
      simp only [resInv]
      linarith
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (h65 _ _).trans ih
  refine ⟨?_, fun hpA hpB => ?_⟩
  · -- (ii)
    obtain ⟨f0, hf0⟩ := hfix
    have h53 := proposition_5_3 A B hA hB JA JB hJA hJB v vD vR hv hvD hvR h12 f0 hf0
    refine ⟨?_, ?_⟩
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨‖x - f0‖ + ‖JA f0‖, ?_⟩
      rintro _ ⟨n, rfl⟩
      obtain ⟨-, hJ, -⟩ := h53 n
      have hd := hdec x f0 n
      have h1 : ‖JA (T^[n] x) - JA (T^[n] f0)‖ ≤ ‖x - f0‖ := by
        have : ‖JA (T^[n] x) - JA (T^[n] f0)‖ ^ 2 ≤ ‖x - f0‖ ^ 2 := by
          nlinarith [sq_nonneg ‖resInv JA (T^[n] x) - resInv JA (T^[n] f0)‖]
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
      have e : JA (T^[n] x) + (n : ℝ) • vR = (JA (T^[n] x) - JA (T^[n] f0)) + JA f0 := by
        rw [hJ]; abel
      show ‖JA (T^[n] x) + (n : ℝ) • vR‖ ≤ _
      rw [e]
      exact (norm_add_le _ _).trans (by linarith)
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨‖x - f0‖ + ‖resInv JA f0‖, ?_⟩
      rintro _ ⟨n, rfl⟩
      obtain ⟨-, -, hJ, -⟩ := h53 n
      have hd := hdec x f0 n
      have h1 : ‖resInv JA (T^[n] x) - resInv JA (T^[n] f0)‖ ≤ ‖x - f0‖ := by
        have : ‖resInv JA (T^[n] x) - resInv JA (T^[n] f0)‖ ^ 2 ≤ ‖x - f0‖ ^ 2 := by
          nlinarith [sq_nonneg ‖JA (T^[n] x) - JA (T^[n] f0)‖]
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
      have e : resInv JA (T^[n] x) + (n : ℝ) • vD =
          (resInv JA (T^[n] x) - resInv JA (T^[n] f0)) + resInv JA f0 := by
        rw [hJ]; abel
      show ‖resInv JA (T^[n] x) + (n : ℝ) • vD‖ ≤ _
      rw [e]
      exact (norm_add_le _ _).trans (by linarith)
  · -- (ix)
    rintro ⟨z, k⟩ ⟨⟨a, ha, b, hb, hab⟩, ⟨z', hk1, hk2⟩⟩ n
    -- Fact 2.4(i): `(z, k) ∈ S`
    have m1 := hpA.1 _ _ _ _ ha hk1
    have m2 := hpB.1 _ _ _ _ hb hk2
    have hbk : b - -k = -(a - (k + v)) := by
      have : b = v - a := by
        have : b = -(-v + a) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hab
        rw [this]; abel
      rw [this]; abel
    have ezz : z - v - (z' - v) = z - z' := by abel
    rw [hbk, ezz, inner_neg_right] at m2
    have h0 : ⟪z - z', a - (k + v)⟫_ℝ = 0 := by linarith
    have hkA : k + v ∈ A z := (hpA.2 _ _ _ _ ha hk1 h0).1
    have h0' : ⟪z - v - (z' - v), b - -k⟫_ℝ = 0 := by
      rw [hbk, ezz, inner_neg_right, h0, neg_zero]
    have hkB : -k ∈ B (z - v) := (hpB.2 _ _ _ _ hb hk2 h0').1
    -- the point `f = z + k + v ∈ Fix(v + T)`
    set f := z + k + v with hf
    have hJf : JA f = z := DR55Aux.res_unique A hA.1 JA hJA (by rw [hf]; abel_nf; simpa [add_comm] using hkA)
    have hRf : refl JA f = z - k - v := by
      simp only [InconsistentDR.Shadow.refl]; rw [hJf, hf]; module
    have hJBf : JB (refl JA f) = z - v := by
      rw [hRf]
      apply DR55Aux.res_unique B hB.1 JB hJB
      have : z - k - v - (z - v) = -k := by abel
      rw [this]; exact hkB
    have hfix' : f ∈ FixSet (fun y => v + drT JA JB y) := by
      show v + drT JA JB f = f
      simp only [drT]; rw [hJBf, hJf]; abel
    obtain ⟨-, hJn, hJn', -⟩ := proposition_5_3 A B hA hB JA JB hJA hJB v vD vR hv hvD hvR h12 f
      hfix' n
    obtain ⟨-, hJn1, hJn1', -⟩ := proposition_5_3 A B hA hB JA JB hJA hJB v vD vR hv hvD hvR h12 f
      hfix' (n + 1)
    have hres : resInv JA f = k + v := by simp only [resInv]; rw [hJf, hf]; abel
    have e1 : ∀ m : ℕ, JA (T^[m] f) = z - (m : ℝ) • vR →
        JA (T^[m] x) + (m : ℝ) • vR - z = JA (T^[m] x) - JA (T^[m] f) := by
      intro m hm; rw [hm]; abel
    have e2 : ∀ m : ℕ, resInv JA (T^[m] f) = k + v - (m : ℝ) • vD →
        -v + (resInv JA (T^[m] x) + (m : ℝ) • vD) - k = resInv JA (T^[m] x) - resInv JA (T^[m] f) := by
      intro m hm; rw [hm]; abel
    show ‖JA (T^[n + 1] x) + ((n + 1 : ℕ) : ℝ) • vR - z‖ ^ 2 +
        ‖-v + (resInv JA (T^[n + 1] x) + ((n + 1 : ℕ) : ℝ) • vD) - k‖ ^ 2 ≤
      ‖JA (T^[n] x) + (n : ℝ) • vR - z‖ ^ 2 + ‖-v + (resInv JA (T^[n] x) + (n : ℝ) • vD) - k‖ ^ 2
    rw [e1 n (by rw [hJn, hJf]), e2 n (by rw [hJn', hres]),
      e1 (n + 1) (by rw [hJn1, hJf]), e2 (n + 1) (by rw [hJn1', hres])]
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact h65 _ _
