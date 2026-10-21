-- Prove2me | solution 1 for NesterovRCD.HighProb.theorem2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:09:38.344671+00:00
-- url     : https://prove2.me/submissions/c3826c7e-4189-42d2-8c65-80ba1a2c2b90

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
set_option autoImplicit false
open NesterovRCD.Sublinear NesterovRCD.HighProb

theorem NHP_sharp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (s : F →L[ℝ] ℝ) (v : F)
    (h : IsSharp s v) : s v = ‖v‖ ^ 2 ∧ ‖v‖ = ‖s‖ := by
  have h1 : ∀ t : ℝ, 0 ≤ (‖v‖ ^ 2 / 2) * (t * t) + (-(s v)) * t + (s v - ‖v‖ ^ 2 / 2) := by
    intro t
    have := h (t • v)
    simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at this
    nlinarith
  have hd := discrim_le_zero h1
  unfold discrim at hd
  have hsv : s v = ‖v‖ ^ 2 := by
    have : (s v - ‖v‖ ^ 2) ^ 2 ≤ 0 := by nlinarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
    linarith
  refine ⟨hsv, ?_⟩
  have hbd : ∀ w : F, ‖s w‖ ≤ ‖v‖ * ‖w‖ := by
    intro w
    have h2 : ∀ t : ℝ, 0 ≤ (‖w‖ ^ 2 / 2) * (t * t) + (-(s w)) * t + ‖v‖ ^ 2 / 2 := by
      intro t
      have := h (t • w)
      simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at this
      rw [hsv] at this
      nlinarith
    have hd2 := discrim_le_zero h2
    unfold discrim at hd2
    have : (s w) ^ 2 ≤ (‖v‖ * ‖w‖) ^ 2 := by nlinarith
    rw [Real.norm_eq_abs]
    exact abs_le_of_sq_le_sq this (by positivity) |> fun h => h
  have h3 : ‖s‖ ≤ ‖v‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) hbd
  have h4 : ‖v‖ ^ 2 ≤ ‖s‖ * ‖v‖ := by
    rw [← hsv]; exact (le_abs_self _).trans (s.le_opNorm v)
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · rw [← h0] at h3 ⊢; linarith [norm_nonneg s]
  · have : ‖v‖ ≤ ‖s‖ := by nlinarith
    linarith

theorem NHP_descent {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (f : Blocks E → ℝ) (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (i : Fin n) (x : Blocks E) (h : E i) :
    f (x + Pi.single i h) ≤ f x + partialGrad f x i h + L i / 2 * ‖h‖ ^ 2 := by
  obtain ⟨hdiff, hLpos, hlip⟩ := hL
  set e : Blocks E := Pi.single i h with he
  set g : ℝ → ℝ := fun t => f (x + t • e) with hg
  have hder : ∀ t : ℝ, HasDerivAt g (partialGrad f (x + t • e) i h) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add x
    have h2 : HasDerivAt g (fderiv ℝ f (x + t • e) e) t :=
      (hdiff (x + t • e)).hasFDerivAt.comp_hasDerivAt t h1
    have e1 : partialGrad f (x + t • e) i h = fderiv ℝ f (x + t • e) e := by
      simp [partialGrad, he]
    rw [e1]; exact h2
  have hkey : ∀ t : ℝ, |partialGrad f (x + t • e) i h - partialGrad f x i h| ≤ L i * |t| * ‖h‖ ^ 2 := by
    intro t
    have : x + t • e = x + Pi.single i (t • h) := by
      simp [he, Pi.single_smul]
    rw [this]
    have h1 := hlip i x (t • h)
    have h2 := (partialGrad f (x + Pi.single i (t • h)) i - partialGrad f x i).le_opNorm h
    have h3 : partialGrad f (x + Pi.single i (t • h)) i h - partialGrad f x i h =
        (partialGrad f (x + Pi.single i (t • h)) i - partialGrad f x i) h := rfl
    rw [h3]
    rw [norm_smul, Real.norm_eq_abs] at h1
    calc |(partialGrad f (x + Pi.single i (t • h)) i - partialGrad f x i) h|
        ≤ ‖partialGrad f (x + Pi.single i (t • h)) i - partialGrad f x i‖ * ‖h‖ := by
          simpa [Real.norm_eq_abs] using h2
      _ ≤ (L i * (|t| * ‖h‖)) * ‖h‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = L i * |t| * ‖h‖ ^ 2 := by ring
  set G : ℝ → ℝ := fun t => g t - g 0 - t * partialGrad f x i h - (L i * ‖h‖ ^ 2 / 2) * t ^ 2 with hG
  have hGder : ∀ t : ℝ, HasDerivAt G (partialGrad f (x + t • e) i h - partialGrad f x i h
      - L i * ‖h‖ ^ 2 * t) t := by
    intro t
    have h0 : g 0 = g 0 := rfl
    have := (((hder t).sub (hasDerivAt_const t (g 0))).sub ((hasDerivAt_id t).mul_const (partialGrad f x i h))).sub
      (((hasDerivAt_pow 2 t).const_mul (L i * ‖h‖ ^ 2 / 2)))
    refine HasDerivAt.congr_deriv this ?_
    norm_num
    ring
  have hanti : AntitoneOn G (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (fun t _ => (hGder t).continuousAt.continuousWithinAt)
      (fun t _ => (hGder t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    have ht' : 0 < t := ht
    rw [(hGder t).deriv]
    have := hkey t
    rw [abs_of_pos ht'] at this
    have := (abs_le.1 (hkey t)).2
    rw [abs_of_pos ht'] at this
    nlinarith
  have h01 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
  have hg1 : g 1 = f (x + e) := by simp [hg]
  have hg0 : g 0 = f x := by simp [hg]
  simp only [hG, hg1, hg0] at h01
  have := (hder 0).deriv
  simp at h01 ⊢
  have hpg : partialGrad f x i h = partialGrad f (x + (0:ℝ) • e) i h := by simp
  nlinarith

theorem NHP_step {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (f : Blocks E → ℝ) (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp) (i : Fin n) (x : Blocks E) :
    f (coordStep f L sharp i x) ≤ f x - (1 / (2 * L i)) * ‖partialGrad f x i‖ ^ 2 := by
  have hLi : 0 < L i := hL.2.1 i
  obtain ⟨h1, h2⟩ := NHP_sharp (partialGrad f x i) (sharp i (partialGrad f x i)) (hsharp i _)
  set s := partialGrad f x i with hs
  set v := sharp i s with hv
  have hstep : coordStep f L sharp i x = x + Pi.single i (-((L i)⁻¹ • v)) := by
    unfold coordStep
    rw [sub_eq_add_neg, ← Pi.single_neg]
  rw [hstep]
  have hd := NHP_descent f L hL i x (-((L i)⁻¹ • v))
  have e1 : partialGrad f x i (-((L i)⁻¹ • v)) = -((L i)⁻¹ * ‖s‖ ^ 2) := by
    rw [← hs, map_neg, map_smul, smul_eq_mul, h1, h2]
  have e2 : ‖-((L i)⁻¹ • v)‖ ^ 2 = (L i)⁻¹ ^ 2 * ‖s‖ ^ 2 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hLi), mul_pow, h2]
  rw [e1, e2] at hd
  have : f x + -((L i)⁻¹ * ‖s‖ ^ 2) + L i / 2 * ((L i)⁻¹ ^ 2 * ‖s‖ ^ 2) =
      f x - (1 / (2 * L i)) * ‖s‖ ^ 2 := by
    field_simp; ring
  linarith

theorem NHP_prob_sum {n : ℕ} (hn : 0 < n) (L : Fin n → ℝ) (hpos : ∀ i, 0 < L i) (α : ℝ) :
    0 < S L α ∧ ∑ i, prob L α i = 1 := by
  have hS : 0 < S L α := by
    unfold S
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hpos i) α) Finset.univ_nonempty
  refine ⟨hS, ?_⟩
  unfold prob
  rw [← Finset.sum_div]
  exact div_self hS.ne'

theorem NHP_avg {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (hn : 0 < n) (f : Blocks E → ℝ) (L : Fin n → ℝ) (hL : CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : IsSharpSelection sharp) (α : ℝ) (x : Blocks E) :
    ∑ i, prob L α i * f (coordStep f L sharp i x) ≤
      f x - (∑ i, (L i ^ (1 - α))⁻¹ * ‖partialGrad f x i‖ ^ 2) / (2 * S L α) := by
  obtain ⟨hS, hsum⟩ := NHP_prob_sum hn L hL.2.1 α
  have hp : ∀ i, 0 ≤ prob L α i := fun i => by
    unfold prob; exact div_nonneg (Real.rpow_nonneg (hL.2.1 i).le _) hS.le
  calc ∑ i, prob L α i * f (coordStep f L sharp i x)
      ≤ ∑ i, prob L α i * (f x - (1 / (2 * L i)) * ‖partialGrad f x i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (NHP_step f L hL sharp hsharp i x) (hp i)
    _ = f x - (∑ i, (L i ^ (1 - α))⁻¹ * ‖partialGrad f x i‖ ^ 2) / (2 * S L α) := by
        have : ∀ i, prob L α i * (f x - (1 / (2 * L i)) * ‖partialGrad f x i‖ ^ 2) =
            prob L α i * f x - ((L i ^ (1 - α))⁻¹ * ‖partialGrad f x i‖ ^ 2) / (2 * S L α) := by
          intro i
          have hLi := hL.2.1 i
          have h1 : L i ^ (1 - α) = L i / L i ^ α := by
            rw [Real.rpow_sub hLi, Real.rpow_one]
          have h2 : 0 < L i ^ α := Real.rpow_pos_of_pos hLi α
          unfold prob
          rw [h1]
          field_simp
        simp only [this]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, ← Finset.sum_div]
        ring

theorem NHP_gd {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (f : Blocks E → ℝ) (L : Fin n → ℝ) (hLpos : ∀ i, 0 < L i)
    (α σ : ℝ) (hσ : 0 < σ) (hsc : StronglyConvexW f L (1 - α) σ) (x y : Blocks E) :
    f x - (∑ i, (L i ^ (1 - α))⁻¹ * ‖partialGrad f x i‖ ^ 2) / (2 * σ) ≤ f y := by
  have h := hsc.2 x y
  set h' : Blocks E := y - x with hh'
  have hdec : fderiv ℝ f x h' = ∑ i, partialGrad f x i (h' i) := by
    conv_lhs => rw [← Finset.univ_sum_single h']
    rw [map_sum]
    rfl
  have hw : wnorm L (1 - α) h' ^ 2 = ∑ i, L i ^ (1 - α) * ‖h' i‖ ^ 2 := by
    unfold wnorm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (hLpos i).le _) (sq_nonneg _)
  rw [hdec, hw] at h
  have hblock : ∀ i, -((L i ^ (1 - α))⁻¹ * ‖partialGrad f x i‖ ^ 2) / (2 * σ) ≤
      partialGrad f x i (h' i) + σ / 2 * (L i ^ (1 - α) * ‖h' i‖ ^ 2) := by
    intro i
    have hw0 : 0 < L i ^ (1 - α) := Real.rpow_pos_of_pos (hLpos i) _
    set a := ‖partialGrad f x i‖ with ha
    set r := ‖h' i‖ with hr
    set w := L i ^ (1 - α) with hwdef
    have h1 : -(a * r) ≤ partialGrad f x i (h' i) := by
      have := (partialGrad f x i).le_opNorm (h' i)
      have := neg_abs_le (partialGrad f x i (h' i))
      simp only [Real.norm_eq_abs] at *
      linarith
    have h2 : -(w⁻¹ * a ^ 2) / (2 * σ) ≤ -(a * r) + σ / 2 * (w * r ^ 2) := by
      have : 0 ≤ (σ * w * r - a) ^ 2 / (2 * σ * w) := by positivity
      have e : (σ * w * r - a) ^ 2 / (2 * σ * w) = -(a * r) + σ / 2 * (w * r ^ 2) + w⁻¹ * a ^ 2 / (2 * σ) := by
        field_simp; ring
      have e2 : -(w⁻¹ * a ^ 2) / (2 * σ) = -(w⁻¹ * a ^ 2 / (2 * σ)) := by ring
      rw [e2]; linarith
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hblock i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have e3 : ∑ i, -((L i ^ (1 - α))⁻¹ * ‖partialGrad f x i‖ ^ 2) / (2 * σ) =
      -((∑ i, (L i ^ (1 - α))⁻¹ * ‖partialGrad f x i‖ ^ 2) / (2 * σ)) := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib]; ring
  rw [e3] at hsum
  have : ∑ i, partialGrad f x i (h' i) + σ / 2 * ∑ i, L i ^ (1 - α) * ‖h' i‖ ^ 2 =
      ∑ i, partialGrad f x i (h' i) + σ / 2 * ∑ i, L i ^ (1 - α) * ‖h' i‖ ^ 2 := rfl
  linarith

theorem NHP_expect_succ {n k : ℕ} (p : Fin n → ℝ) (F : (Fin (k + 1) → Fin n) → ℝ) :
    expect p (k + 1) F = expect p k (fun idx' => ∑ i, p i * F (Fin.snoc (α := fun _ => Fin n) idx' i)) := by
  unfold expect
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => Fin n)).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun idx' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.snocEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  have e : (Fin.snocEquiv fun _ : Fin (k + 1) => Fin n) (i, idx') = Fin.snoc idx' i := rfl
  rw [e]
  ring

theorem NHP_expect_zero {n : ℕ} (p : Fin n → ℝ) (F : (Fin 0 → Fin n) → ℝ) :
    expect p 0 F = F (fun i => i.elim0) := by
  unfold expect
  have hu : ∀ idx : Fin 0 → Fin n, idx = (fun i => i.elim0) := fun idx => Subsingleton.elim _ _
  rw [Finset.sum_eq_single (fun i => i.elim0)]
  · simp
  · intro b _ hb; exact absurd (hu b) hb
  · intro h; exact absurd (Finset.mem_univ _) h

theorem NHP_expect_const {n : ℕ} (p : Fin n → ℝ) (hp : ∑ i, p i = 1) (k : ℕ) (c : ℝ) :
    expect p k (fun _ => c) = c := by
  induction k with
  | zero => rw [NHP_expect_zero]
  | succ k ih =>
    rw [NHP_expect_succ]
    simp only [← Finset.sum_mul, hp, one_mul]
    exact ih

theorem NHP_expect_mono {n k : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (F G : (Fin k → Fin n) → ℝ) (h : ∀ idx, F idx ≤ G idx) : expect p k F ≤ expect p k G := by
  unfold expect
  exact Finset.sum_le_sum fun idx _ => mul_le_mul_of_nonneg_left (h idx)
    (Finset.prod_nonneg fun s _ => hp _)

theorem NHP_expect_sub {n k : ℕ} (p : Fin n → ℝ) (F : (Fin k → Fin n) → ℝ) (c : ℝ)
    (hp : ∑ i, p i = 1) : expect p k (fun idx => F idx - c) = expect p k F - c := by
  have : expect p k (fun idx => F idx - c) = expect p k F - expect p k (fun _ => c) := by
    unfold expect
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun idx _ => by ring
  rw [this, NHP_expect_const p hp]

theorem NHP_expect_mul {n k : ℕ} (p : Fin n → ℝ) (F : (Fin k → Fin n) → ℝ) (r : ℝ) :
    expect p k (fun idx => r * F idx) = r * expect p k F := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun idx _ => by ring

theorem NHP_expect_nonneg {n k : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (F : (Fin k → Fin n) → ℝ) (h : ∀ idx, 0 ≤ F idx) : 0 ≤ expect p k F := by
  unfold expect
  exact Finset.sum_nonneg fun idx _ => mul_nonneg (Finset.prod_nonneg fun s _ => hp _) (h idx)

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem solution (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) (hsharp : NesterovRCD.Sublinear.IsSharpSelection sharp)
    (α σ : ℝ) (hσ : 0 < σ) (hsc : StronglyConvexW f L (1 - α) σ)
    (x0 xs : NesterovRCD.Sublinear.Blocks E) (hxs : NesterovRCD.Sublinear.IsMinimizer f xs) (k : ℕ) :
    NesterovRCD.Sublinear.expect (NesterovRCD.Sublinear.prob L α) k (fun idx => f (NesterovRCD.Sublinear.rcdm f L sharp x0 k idx)) - f xs
      ≤ (1 - σ / NesterovRCD.Sublinear.S L α) ^ k * (f x0 - f xs) := by
  obtain ⟨hS, hsum⟩ := NHP_prob_sum hn L hL.2.1 α
  have hq : ∀ i, 0 ≤ prob L α i := fun i => by
    unfold prob; exact div_nonneg (Real.rpow_nonneg (hL.2.1 i).le _) hS.le
  set r : ℝ := 1 - σ / S L α with hr
  set A : ℕ → ℝ := fun m => expect (prob L α) m (fun idx => f (rcdm f L sharp x0 m idx) - f xs) with hA
  have hA0 : A 0 = f x0 - f xs := by
    simp only [hA]
    rw [NHP_expect_zero]
    rfl
  have hAnn : ∀ m, 0 ≤ A m := fun m =>
    NHP_expect_nonneg _ hq _ fun idx => sub_nonneg.2 (hxs _)
  have hstep : ∀ m, A (m + 1) ≤ r * A m := by
    intro m
    simp only [hA]
    rw [NHP_expect_succ, ← NHP_expect_mul]
    refine NHP_expect_mono _ hq _ _ fun idx' => ?_
    set y := rcdm f L sharp x0 m idx' with hy
    have hrc : ∀ i : Fin n, rcdm f L sharp x0 (m + 1) (Fin.snoc (α := fun _ => Fin n) idx' i) =
        coordStep f L sharp i y := by
      intro i
      simp [rcdm, hy]
    simp only [hrc]
    have h1 := NHP_avg hn f L hL sharp hsharp α y
    have h2 := NHP_gd f L hL.2.1 α σ hσ hsc y xs
    have e : ∑ i, prob L α i * (f (coordStep f L sharp i y) - f xs) =
        ∑ i, prob L α i * f (coordStep f L sharp i y) - f xs := by
      rw [show (∑ i, prob L α i * (f (coordStep f L sharp i y) - f xs)) =
        ∑ i, prob L α i * f (coordStep f L sharp i y) - (∑ i, prob L α i) * f xs by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring, hsum, one_mul]
    rw [e]
    set W := ∑ i, (L i ^ (1 - α))⁻¹ * ‖partialGrad f y i‖ ^ 2 with hW
    have hW' : 2 * σ * (f y - f xs) ≤ W := by
      have : f y - W / (2 * σ) ≤ f xs := h2
      have h3 : W / (2 * σ) ≥ f y - f xs := by linarith
      rw [ge_iff_le, le_div_iff₀ (by positivity)] at h3
      linarith
    have h4 : σ * (f y - f xs) / S L α ≤ W / (2 * S L α) := by
      rw [div_le_div_iff₀ hS (by positivity)]
      nlinarith
    have : r * (f y - f xs) = (f y - f xs) - σ * (f y - f xs) / S L α := by
      rw [hr]; field_simp
    rw [this]
    linarith
  have hfin : ∀ m, A m ≤ r ^ m * A 0 := by
    rcases (hAnn 0).eq_or_lt with h0 | h0
    · intro m
      have : ∀ m, A m = 0 := by
        intro m
        induction m with
        | zero => exact h0.symm
        | succ m ih =>
          have := hstep m
          rw [ih, mul_zero] at this
          exact le_antisymm this (hAnn _)
      rw [this m, ← h0]; simp
    · have hr0 : 0 ≤ r := by
        have := hstep 0
        have h1 := hAnn 1
        by_contra hneg
        push_neg at hneg
        nlinarith
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        calc A (m + 1) ≤ r * A m := hstep m
          _ ≤ r * (r ^ m * A 0) := mul_le_mul_of_nonneg_left ih hr0
          _ = r ^ (m + 1) * A 0 := by ring
  have := hfin k
  have e : expect (prob L α) k (fun idx => f (rcdm f L sharp x0 k idx)) - f xs = A k := by
    simp only [hA]
    rw [NHP_expect_sub _ _ _ hsum]
  rw [e]
  rw [hA0] at this
  exact this

