-- Prove2me | solution 1 for LoopTwoGroup.Equiv.lemma_5_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:44:56.824126+00:00
-- url     : https://prove2.me/submissions/3e602b41-5904-4935-baf1-b115f7910862

import Definitions.Def_LoopTwoGroup_Equiv_Model
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Theorems.Thm_LoopTwoGroup_Equiv_lemma_5_4
import Theorems.Thm_LoopTwoGroup_Equiv_lemma_5_7
import Mathlib.Tactic.Abel


set_option autoImplicit false
open LoopTwoGroup.Equiv MeasureTheory InnerProductSpace Set

namespace Loop58Work

variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]

lemma twoPi_pos : 0 < 2 * Real.pi := mul_pos zero_lt_two Real.pi_pos

lemma clamp_eq_of_mem {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) : clamp t = t := by
  rw [clamp, min_eq_left ht.2, max_eq_right ht.1]

lemma clamp_endpoint : clamp (2 * Real.pi) = 2 * Real.pi :=
  clamp_eq_of_mem ⟨twoPi_pos.le, le_rfl⟩

lemma psi_deriv (L : InvLieBracket g) (k : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi)))
    (Ψ : LInfHom (gk L k) (Pk L k)) (hΨ : PsiComponents L k f Ψ)
    (a : g) {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    dpath (Ψ.f0 a).1 t = derivWithin f (Icc 0 (2 * Real.pi)) t • a := by
  have heq : EqOn (Ψ.f0 a).1 (fun s => f s • a) (Icc 0 (2 * Real.pi)) := by
    intro s hs
    change (Ψ.f0 a).1 s = f s • a
    rw [hΨ.1 a s, clamp_eq_of_mem hs]
  calc
    dpath (Ψ.f0 a).1 t = derivWithin (fun s => f s • a) (Icc 0 (2 * Real.pi)) t :=
      derivWithin_congr heq (heq ht)
    _ = _ := derivWithin_smul_const (hf.differentiableOn (by simp) t ht) a

lemma phi_psi_f2_zero (L : InvLieBracket g) (k : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Icc 0 (2 * Real.pi)))
    (Φ : LInfHom (Pk L k) (gk L k)) (hΦ : PhiComponents L k Φ)
    (Ψ : LInfHom (gk L k) (Pk L k)) (hΨ : PsiComponents L k f Ψ) (a b : g) :
    Φ.f2 (Ψ.f0 a) (Ψ.f0 b) = 0 := by
  rw [hΦ.2.2]
  have hi : (∫ t in (0 : ℝ)..(2 * Real.pi),
      (⟪(Ψ.f0 b).1 t, dpath (Ψ.f0 a).1 t⟫_ℝ -
        ⟪dpath (Ψ.f0 b).1 t, (Ψ.f0 a).1 t⟫_ℝ)) = 0 := by
    calc
      _ = ∫ _ in (0 : ℝ)..(2 * Real.pi), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        have ht' : t ∈ Icc 0 (2 * Real.pi) := by
          simpa only [uIcc_of_le twoPi_pos.le] using ht
        rw [psi_deriv L k f hf Ψ hΨ a ht', psi_deriv L k f hf Ψ hΨ b ht',
          hΨ.1 a t, hΨ.1 b t, clamp_eq_of_mem ht']
        simp only [real_inner_smul_left, real_inner_smul_right]
        ring
      _ = 0 := by simp
  rw [hi, mul_zero]

lemma f2_neg_left {L : InvLieBracket g} {k : ℝ}
    (Φ : LInfHom (Pk L k) (gk L k)) (p q : pathSpace g) :
    Φ.f2 (-p) q = -Φ.f2 p q := by
  simpa only [neg_one_smul] using Φ.f2_smul (-1) p q

lemma f2_add_right {L : InvLieBracket g} {k : ℝ}
    (Φ : LInfHom (Pk L k) (gk L k)) (p q r : pathSpace g) :
    Φ.f2 p (q + r) = Φ.f2 p q + Φ.f2 p r := by
  calc
    Φ.f2 p (q + r) = -Φ.f2 (q + r) p := Φ.f2_skew p (q + r)
    _ = -(Φ.f2 q p + Φ.f2 r p) := congrArg Neg.neg (Φ.f2_add q r p)
    _ = -Φ.f2 q p + -Φ.f2 r p := neg_add _ _
    _ = Φ.f2 p q + Φ.f2 p r := by rw [← Φ.f2_skew p q, ← Φ.f2_skew p r]

lemma f2_neg_right {L : InvLieBracket g} {k : ℝ}
    (Φ : LInfHom (Pk L k) (gk L k)) (p q : pathSpace g) :
    Φ.f2 p (-q) = -Φ.f2 p q := by
  rw [Φ.f2_skew p (-q), f2_neg_left, neg_neg, Φ.f2_skew q p]

lemma f2_sub_right {L : InvLieBracket g} {k : ℝ}
    (Φ : LInfHom (Pk L k) (gk L k)) (p q r : pathSpace g) :
    Φ.f2 p (q - r) = Φ.f2 p q - Φ.f2 p r := by
  rw [sub_eq_add_neg, f2_add_right, f2_neg_right, sub_eq_add_neg]

end Loop58Work


set_option autoImplicit false
open LoopTwoGroup.Equiv Loop58Work MeasureTheory InnerProductSpace

theorem solution {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] (L : InvLieBracket g) (k : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) (hf1 : f (2 * Real.pi) = 1) :
    ∃ (Φ : LInfHom (Pk L k) (gk L k)) (Ψ : LInfHom (gk L k) (Pk L k)),
      PhiComponents L k Φ ∧ PsiComponents L k f Ψ ∧
      compF0 Ψ Φ = LinearMap.id ∧ compF1 Ψ Φ = LinearMap.id ∧
      (∀ a b, compF2 Ψ Φ a b = 0) ∧
      ∃ T : TwoHom (Pk L k) (Pk L k)
        (compF0 Φ Ψ) LinearMap.id (compF1 Φ Ψ) LinearMap.id
        (compF2 Φ Ψ) (fun _ _ => 0),
        (∀ p t, ((T.τ p).1).1 t = p.1 t - f (clamp t) • p.1 (2 * Real.pi)) ∧
        (∀ p, (T.τ p).2 = 0) := by
  obtain ⟨Φ, hΦ⟩ := lemma_5_4 L k
  obtain ⟨Ψ, hΨ⟩ := lemma_5_7 L k f hf hf0 hf1
  have h00 (a : g) : Φ.f0 (Ψ.f0 a) = a := by
    rw [hΦ.1, hΨ.1, clamp_endpoint, hf1, one_smul]
  have h11 (c : ℝ) : Φ.f1 (Ψ.f1 c) = c := by
    rw [hΨ.2.1, hΦ.2.1]
  have hPhiD (h : loopSpace g × ℝ) : Φ.f0 ((Pk L k).d h) = 0 :=
    (hΦ.1 ((Pk L k).d h)).trans h.1.2.2
  have hPhiBr (a b : pathSpace g) :
      Φ.f0 (pathBracket L a b) = L.br (Φ.f0 a) (Φ.f0 b) := by
    have h := Φ.eq3 a b
    change (0 : g) = Φ.f0 (pathBracket L a b) - L.br (Φ.f0 a) (Φ.f0 b) at h
    exact sub_eq_zero.mp h.symm
  have skew (a b : g) : L.br a b = -L.br b a := by
    have h := L.self (a + b)
    simp only [map_add, ContinuousLinearMap.add_apply] at h
    rw [L.self a, L.self b, zero_add, add_zero] at h
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  let S : pathSpace g →ₗ[ℝ] pathSpace g := Ψ.f0.comp Φ.f0
  let D : pathSpace g →ₗ[ℝ] pathSpace g := LinearMap.id - S
  let δ : pathSpace g →ₗ[ℝ] loopSpace g := {
    toFun := fun p => ⟨(D p).1, (D p).2, by
      change p.1 (2 * Real.pi) - (Ψ.f0 (Φ.f0 p)).1 (2 * Real.pi) = 0
      rw [← hΦ.1 p, ← hΦ.1 (Ψ.f0 (Φ.f0 p)), h00, sub_self]⟩
    map_add' := by
      intro a b
      apply Subtype.ext
      exact congrArg (fun p : pathSpace g => p.1) (D.map_add a b)
    map_smul' := by
      intro r a
      apply Subtype.ext
      exact congrArg (fun p : pathSpace g => p.1) (D.map_smul r a) }
  let τ : pathSpace g →ₗ[ℝ] (loopSpace g × ℝ) := δ.prod 0
  have ht0 (a : pathSpace g) : (Pk L k).d (τ a) = a - S a := by
    apply Subtype.ext
    rfl
  have ht1 (h : loopSpace g × ℝ) : τ ((Pk L k).d h) = h - Ψ.f1 (Φ.f1 h) := by
    apply Prod.ext
    · apply Subtype.ext
      funext t
      change h.1.1 t - (Ψ.f0 (Φ.f0 ((Pk L k).d h))).1 t =
        h.1.1 t - (Ψ.f1 (Φ.f1 h)).1.1 t
      rw [hPhiD, map_zero, hΨ.2.1]
      rfl
    · change (0 : ℝ) = h.2 - (Ψ.f1 (Φ.f1 h)).2
      rw [hΨ.2.1, hΦ.2.1, sub_self]
  have action (p : pathSpace g) (h : loopSpace g × ℝ) :
      ((Pk L k).l2h p h).2 = Φ.f2 p ((Pk L k).d h) := by
    have he := Φ.eq4 p h
    rw [hΦ.2.1] at he
    change Φ.f2 p ((Pk L k).d h) = ((Pk L k).l2h p h).2 - 0 at he
    simpa only [sub_zero] using he.symm
  let T : TwoHom (Pk L k) (Pk L k)
      (compF0 Φ Ψ) LinearMap.id (compF1 Φ Ψ) LinearMap.id
      (compF2 Φ Ψ) (fun _ _ => 0) := {
    τ := τ
    hom0 := ht0
    hom1 := ht1
    eq7 := by
      intro a b
      apply Prod.ext
      · apply Subtype.ext
        funext t
        have he := congrArg (fun p : pathSpace g => p.1 t) (Ψ.eq3 (Φ.f0 a) (Φ.f0 b))
        change (Ψ.f2 (Φ.f0 a) (Φ.f0 b)).1.1 t =
          (Ψ.f0 (L.br (Φ.f0 a) (Φ.f0 b))).1 t - L.br ((S a).1 t) ((S b).1 t) at he
        rw [← hPhiBr a b] at he
        change (Ψ.f2 (Φ.f0 a) (Φ.f0 b)).1.1 t =
          (S (pathBracket L a b)).1 t - L.br ((S a).1 t) ((S b).1 t) at he
        change (Ψ.f2 (Φ.f0 a) (Φ.f0 b)).1.1 t + (Ψ.f1 (Φ.f2 a b)).1.1 t - 0 =
          L.br ((S a).1 t) (b.1 t - (S b).1 t) -
            L.br (b.1 t) (a.1 t - (S a).1 t) -
            (L.br (a.1 t) (b.1 t) - (S (pathBracket L a b)).1 t)
        rw [hΨ.2.1]
        change (Ψ.f2 (Φ.f0 a) (Φ.f0 b)).1.1 t + 0 - 0 = _
        rw [add_zero, sub_zero, he, map_sub, map_sub,
          skew (b.1 t) (a.1 t), skew (b.1 t) ((S a).1 t)]
        abel
      · change (Ψ.f2 (Φ.f0 a) (Φ.f0 b)).2 + (Ψ.f1 (Φ.f2 a b)).2 - 0 =
          ((Pk L k).l2h (S a) (τ b)).2 - ((Pk L k).l2h b (τ a)).2 - 0
        rw [hΨ.2.2.2, hΨ.2.1]
        change (0 : ℝ) + Φ.f2 a b - 0 =
          ((Pk L k).l2h (S a) (τ b)).2 - ((Pk L k).l2h b (τ a)).2 - 0
        rw [zero_add, sub_zero, sub_zero, action, action, ht0, ht0,
          f2_sub_right, f2_sub_right]
        have hz : Φ.f2 (S a) (S b) = 0 :=
          phi_psi_f2_zero L k f hf Φ hΦ Ψ hΨ (Φ.f0 a) (Φ.f0 b)
        rw [hz, Φ.f2_skew b a, Φ.f2_skew b (S a)]
        ring }
  refine ⟨Φ, Ψ, hΦ, hΨ, ?_, ?_, ?_, T, ?_, ?_⟩
  · apply LinearMap.ext
    intro a
    exact h00 a
  · apply LinearMap.ext
    intro c
    exact h11 c
  · intro a b
    change Φ.f2 (Ψ.f0 a) (Ψ.f0 b) + Φ.f1 (Ψ.f2 a b) = 0
    rw [phi_psi_f2_zero L k f hf Φ hΦ Ψ hΨ, hΦ.2.1, hΨ.2.2.2, add_zero]
  · intro p t
    change p.1 t - (Ψ.f0 (Φ.f0 p)).1 t = p.1 t - f (clamp t) • p.1 (2 * Real.pi)
    rw [hΨ.1, hΦ.1]
  · intro p
    rfl
