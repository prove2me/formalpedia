-- Prove2me | solution 1 for GoodViews.optimal_views_minimal_representation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T12:37:37.380811+00:00
-- url     : https://prove2.me/submissions/03baf548-5f19-4b9c-9faf-60ffc65dad1d

import Mathlib
import Definitions.Def_GoodViews_Basic
set_option autoImplicit false
open Finset
namespace GoodViews

lemma entropy_equiv {S α β : Type} [Fintype S] [Fintype α] [Fintype β] (P : S → ℝ)
    (A : S → α) (e : α ≃ β) : entropy P (fun ω => e (A ω)) = entropy P A := by
  unfold entropy
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  unfold law
  congr 1
  ext ω; simp

lemma sum_law_mul {S α : Type} [Fintype S] [Fintype α] (P : S → ℝ) (X : S → α)
    (F : α → ℝ) : ∑ ω, P ω * F (X ω) = ∑ a, law P X a * F a := by
  classical
  unfold law
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ X (fun ω => P ω * F (X ω))]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun ω hω => ?_
  rw [(Finset.mem_filter.1 hω).2]

lemma law_nonneg {S α : Type} [Fintype S] (P : S → ℝ) (hP : ∀ ω, 0 ≤ P ω) (X : S → α)
    (a : α) : 0 ≤ law P X a := by
  unfold law; exact Finset.sum_nonneg fun ω _ => hP ω

lemma le_law {S α : Type} [Fintype S] (P : S → ℝ) (hP : ∀ ω, 0 ≤ P ω) (X : S → α)
    (ω : S) : P ω ≤ law P X (X ω) := by
  classical
  unfold law
  exact Finset.single_le_sum (f := P) (fun ω _ => hP ω)
    (Finset.mem_filter.2 ⟨Finset.mem_univ ω, rfl⟩)

lemma entropy_eq {S α : Type} [Fintype S] [Fintype α] (P : S → ℝ) (X : S → α) :
    entropy P X = -∑ ω, P ω * Real.log (law P X (X ω)) := by
  rw [sum_law_mul P X (fun a => Real.log (law P X a))]
  unfold entropy
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Real.negMulLog]

lemma marg {S α γ : Type} [Fintype S] [Fintype α] [Fintype γ] (P : S → ℝ) (A : S → α)
    (C : S → γ) (c : γ) : ∑ a, law P (fun ω => (A ω, C ω)) (a, c) = law P C c := by
  classical
  have h1 : law P C c = ∑ ω, P ω * (if C ω = c then 1 else 0) := by
    unfold law; rw [Finset.sum_filter]; simp
  have h2 := sum_law_mul P (fun ω => (A ω, C ω)) (fun t => if t.2 = c then (1:ℝ) else 0)
  rw [h1, h2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp

theorem condMutualInfo_nonneg {S α β γ : Type} [Fintype S] [Fintype α] [Fintype β]
    [Fintype γ] (P : S → ℝ) (hP : ∀ ω, 0 ≤ P ω) (A : S → α) (B : S → β) (C : S → γ) :
    0 ≤ condMutualInfo P A B C := by
  set u : S → ℝ := fun ω => law P (fun ω => (A ω, B ω, C ω)) (A ω, B ω, C ω) with hu
  set x : S → ℝ := fun ω => law P (fun ω => (A ω, C ω)) (A ω, C ω) with hx
  set y : S → ℝ := fun ω => law P (fun ω => (B ω, C ω)) (B ω, C ω) with hy
  set c : S → ℝ := fun ω => law P C (C ω) with hc
  have hexp : condMutualInfo P A B C =
      ∑ ω, P ω * (Real.log (u ω) + Real.log (c ω) - Real.log (x ω) - Real.log (y ω)) := by
    unfold condMutualInfo
    rw [entropy_eq P (fun ω => (A ω, C ω)), entropy_eq P (fun ω => (B ω, C ω)),
      entropy_eq P (fun ω => (A ω, B ω, C ω)), entropy_eq P C]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hu, hx, hy, hc]
    ring
  have hpt : ∀ ω, P ω - P ω * (x ω * y ω / (u ω * c ω)) ≤
      P ω * (Real.log (u ω) + Real.log (c ω) - Real.log (x ω) - Real.log (y ω)) := by
    intro ω
    rcases (hP ω).lt_or_eq with h | h
    · have hu0 : 0 < u ω := lt_of_lt_of_le h (le_law P hP _ ω)
      have hx0 : 0 < x ω := lt_of_lt_of_le h (le_law P hP _ ω)
      have hy0 : 0 < y ω := lt_of_lt_of_le h (le_law P hP _ ω)
      have hc0 : 0 < c ω := lt_of_lt_of_le h (le_law P hP _ ω)
      have hz : 0 < x ω * y ω / (u ω * c ω) := by positivity
      have hl := Real.log_le_sub_one_of_pos hz
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul hx0.ne' hy0.ne',
        Real.log_mul hu0.ne' hc0.ne'] at hl
      have h1 : P ω * (x ω * y ω / (u ω * c ω)) - P ω ≥
          P ω * (Real.log (x ω) + Real.log (y ω) - (Real.log (u ω) + Real.log (c ω))) := by
        nlinarith
      linarith
    · rw [← h]; simp
  have hsum : ∑ ω, P ω * (x ω * y ω / (u ω * c ω)) ≤ ∑ ω, P ω := by
    let F : α × β × γ → ℝ := fun t =>
      law P (fun ω => (A ω, C ω)) (t.1, t.2.2) * law P (fun ω => (B ω, C ω)) (t.2.1, t.2.2) /
        (law P (fun ω => (A ω, B ω, C ω)) t * law P C t.2.2)
    have e1 : ∑ ω, P ω * (x ω * y ω / (u ω * c ω)) =
        ∑ t, law P (fun ω => (A ω, B ω, C ω)) t * F t :=
      sum_law_mul P (fun ω => (A ω, B ω, C ω)) F
    have e2 : ∑ t, law P (fun ω => (A ω, B ω, C ω)) t * F t ≤
        ∑ t : α × β × γ, law P (fun ω => (A ω, C ω)) (t.1, t.2.2) *
          law P (fun ω => (B ω, C ω)) (t.2.1, t.2.2) / law P C t.2.2 := by
      refine Finset.sum_le_sum fun t _ => ?_
      have hL := law_nonneg P hP (fun ω => (A ω, B ω, C ω)) t
      have hX : 0 ≤ law P (fun ω => (A ω, C ω)) (t.1, t.2.2) *
          law P (fun ω => (B ω, C ω)) (t.2.1, t.2.2) / law P C t.2.2 := by
        have := law_nonneg P hP (fun ω => (A ω, C ω)) (t.1, t.2.2)
        have := law_nonneg P hP (fun ω => (B ω, C ω)) (t.2.1, t.2.2)
        have := law_nonneg P hP C t.2.2
        positivity
      simp only [F]
      rcases hL.lt_or_eq with h | h
      · rw [mul_div_assoc', mul_div_mul_left _ _ h.ne']
      · rw [← h]; simpa using hX
    have e3 : ∑ t : α × β × γ, law P (fun ω => (A ω, C ω)) (t.1, t.2.2) *
          law P (fun ω => (B ω, C ω)) (t.2.1, t.2.2) / law P C t.2.2 ≤ ∑ ω, P ω := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      have : ∀ b : β, ∑ a : α, ∑ c' : γ, law P (fun ω => (A ω, C ω)) (a, c') *
          law P (fun ω => (B ω, C ω)) (b, c') / law P C c' =
          ∑ c' : γ, ∑ a : α, law P (fun ω => (A ω, C ω)) (a, c') *
          law P (fun ω => (B ω, C ω)) (b, c') / law P C c' := fun b => Finset.sum_comm
      simp only [this]
      rw [Finset.sum_comm]
      have h1 : ∀ c' : γ, ∑ b : β, ∑ a : α, law P (fun ω => (A ω, C ω)) (a, c') *
          law P (fun ω => (B ω, C ω)) (b, c') / law P C c' =
          law P C c' * law P C c' / law P C c' := by
        intro c'
        calc _ = (∑ a : α, law P (fun ω => (A ω, C ω)) (a, c')) *
              (∑ b : β, law P (fun ω => (B ω, C ω)) (b, c')) / law P C c' := by
                rw [Finset.sum_mul_sum, Finset.sum_div, Finset.sum_comm]
                refine Finset.sum_congr rfl fun b _ => ?_
                rw [Finset.sum_div]
          _ = _ := by rw [marg P A C c', marg P B C c']
      simp only [h1]
      have h2 : ∑ ω, P ω = ∑ c' : γ, law P C c' := by
        have := sum_law_mul P C (fun _ => (1:ℝ)); simpa using this
      rw [h2]
      refine Finset.sum_le_sum fun c' _ => ?_
      rcases (law_nonneg P hP C c').lt_or_eq with h | h
      · rw [mul_div_assoc, div_self h.ne', mul_one]
      · rw [← h]; simp
    linarith
  rw [hexp]
  have := Finset.sum_le_sum fun ω (_ : ω ∈ Finset.univ) => hpt ω
  rw [Finset.sum_sub_distrib] at this
  linarith

lemma entropy_unit {S : Type} [Fintype S] (P : S → ℝ) (hP : IsPMF P) :
    entropy P (fun _ : S => ()) = 0 := by
  unfold entropy law
  simp [hP.2]

theorem mutualInfo_nonneg {S α β γ : Type} [Fintype S] [Fintype α] [Fintype β] [Fintype γ]
    (P : S → ℝ) (hP : IsPMF P) (A : S → α) (B : S → β) (C : S → γ) :
    0 ≤ mutualInfo P A B ∧ 0 ≤ condMutualInfo P A B C := by
  refine ⟨?_, condMutualInfo_nonneg P hP.1 A B C⟩
  have h := condMutualInfo_nonneg P hP.1 A B (fun _ => ())
  have e1 := entropy_equiv P (fun ω => (A ω, ())) (Equiv.prodPUnit α)
  have e2 := entropy_equiv P (fun ω => (B ω, ())) (Equiv.prodPUnit β)
  have e3 := entropy_equiv P (fun ω => (A ω, B ω, ()))
    ((Equiv.refl α).prodCongr (Equiv.prodPUnit β))
  simp only [Equiv.prodPUnit_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    id] at e1 e2 e3
  unfold condMutualInfo at h
  unfold mutualInfo
  rw [← e1, ← e2, ← e3, entropy_unit P hP] at h
  linarith

lemma entropy_comp_eq {S α β : Type} [Fintype S] [Fintype α] [Fintype β] (P : S → ℝ)
    (X : S → α) (Y : S → β) (g : α → β) (h : β → α) (hg : ∀ ω, Y ω = g (X ω))
    (hh : ∀ ω, X ω = h (Y ω)) : entropy P X = entropy P Y := by
  rw [entropy_eq, entropy_eq]
  congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 2
  unfold law
  congr 1
  ext ω'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro e; rw [hg ω', hg ω, e]
  · intro e; rw [hh ω', hh ω, e]

lemma cond_zero {S X Y V W : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype V]
    [Fintype W] (P : S → ℝ) (hP : ∀ ω, 0 ≤ P ω) (x : S → X) (y : S → Y) (g : X → V)
    (g' : X → W) (hf : mutualInfo P (g ∘ x) y = mutualInfo P x y) :
    condMutualInfo P y (g' ∘ x) (g ∘ x) = 0 := by
  have n1 := condMutualInfo_nonneg P hP y (g' ∘ x) (g ∘ x)
  have n2 := condMutualInfo_nonneg P hP y x (fun ω => ((g' ∘ x) ω, (g ∘ x) ω))
  have c1 : entropy P (fun ω => (x ω, (g' ∘ x) ω, (g ∘ x) ω)) = entropy P x :=
    entropy_comp_eq P _ _ (fun t => t.1) (fun a => (a, g' a, g a)) (fun _ => rfl) (fun _ => rfl)
  have c2 : entropy P (fun ω => (y ω, x ω, (g' ∘ x) ω, (g ∘ x) ω)) =
      entropy P (fun ω => (x ω, y ω)) :=
    entropy_comp_eq P _ _ (fun t => (t.2.1, t.1)) (fun t => (t.2, t.1, g' t.1, g t.1))
      (fun _ => rfl) (fun _ => rfl)
  have c3 : entropy P (fun ω => (y ω, (g ∘ x) ω)) = entropy P (fun ω => ((g ∘ x) ω, y ω)) :=
    entropy_comp_eq P _ _ (fun t => (t.2, t.1)) (fun t => (t.2, t.1)) (fun _ => rfl) (fun _ => rfl)
  simp only [condMutualInfo, mutualInfo] at *
  linarith

lemma suff_core {S A B Y Z : Type} [Fintype S] [Fintype A] [Fintype B] [Fintype Y]
    [Fintype Z] (P : S → ℝ) (hP : ∀ ω, 0 ≤ P ω) (a : S → A) (b : S → B) (y : S → Y)
    (F : A → Z) (E1 : mutualInfo P a b = mutualInfo P (F ∘ a) b)
    (E2 : condMutualInfo P y a b = 0) :
    mutualInfo P (F ∘ a) y = mutualInfo P a y := by
  have N1 := condMutualInfo_nonneg P hP a y (F ∘ a)
  have N3 := condMutualInfo_nonneg P hP y (F ∘ a) b
  have N4 := condMutualInfo_nonneg P hP a b (fun ω => ((F ∘ a) ω, y ω))
  have q1 : entropy P (fun ω => (a ω, (F ∘ a) ω)) = entropy P a :=
    entropy_comp_eq P _ _ (fun t => t.1) (fun t => (t, F t)) (fun _ => rfl) (fun _ => rfl)
  have q2 : entropy P (fun ω => (y ω, (F ∘ a) ω)) = entropy P (fun ω => ((F ∘ a) ω, y ω)) :=
    entropy_comp_eq P _ _ (fun t => (t.2, t.1)) (fun t => (t.2, t.1)) (fun _ => rfl) (fun _ => rfl)
  have q3 : entropy P (fun ω => (a ω, y ω, (F ∘ a) ω)) = entropy P (fun ω => (a ω, y ω)) :=
    entropy_comp_eq P _ _ (fun t => (t.1, t.2.1)) (fun t => (t.1, t.2, F t.1)) (fun _ => rfl)
      (fun _ => rfl)
  have q4 : entropy P (fun ω => (a ω, (F ∘ a) ω, y ω)) = entropy P (fun ω => (a ω, y ω)) :=
    entropy_comp_eq P _ _ (fun t => (t.1, t.2.2)) (fun t => (t.1, F t.1, t.2)) (fun _ => rfl)
      (fun _ => rfl)
  have q5 : entropy P (fun ω => (b ω, (F ∘ a) ω, y ω)) =
      entropy P (fun ω => (y ω, (F ∘ a) ω, b ω)) :=
    entropy_comp_eq P _ _ (fun t => (t.2.2, t.2.1, t.1)) (fun t => (t.2.2, t.2.1, t.1))
      (fun _ => rfl) (fun _ => rfl)
  have q6 : entropy P (fun ω => (a ω, b ω, (F ∘ a) ω, y ω)) =
      entropy P (fun ω => (y ω, a ω, b ω)) :=
    entropy_comp_eq P _ _ (fun t => (t.2.2.2, t.1, t.2.1)) (fun t => (t.2.1, t.2.2, F t.2.1, t.1))
      (fun _ => rfl) (fun _ => rfl)
  simp only [condMutualInfo, mutualInfo] at *
  linarith

theorem optimal_views_sufficient_representation {S X Y V₁ V₂ Z₁ Z₂ : Type} [Fintype S]
    [Fintype X] [Fintype Y] [Fintype V₁] [Fintype V₂] [Fintype Z₁] [Fintype Z₂]
    (P : S → ℝ) (hP : IsPMF P) (x : S → X) (y : S → Y) (g₁ : X → V₁) (g₂ : X → V₂)
    (hopt : IsOptimalViews P x y g₁ g₂) (f₁ : V₁ → Z₁) (f₂ : V₂ → Z₂)
    (hf₁ : IsMinimalSufficientEncoder P (g₁ ∘ x) (g₂ ∘ x) f₁)
    (hf₂ : IsMinimalSufficientEncoder P (g₂ ∘ x) (g₁ ∘ x) f₂) :
    IsSufficientStat P (g₁ ∘ x) y f₁ ∧ IsSufficientStat P (g₂ ∘ x) y f₂ :=
  ⟨suff_core P hP.1 (g₁ ∘ x) (g₂ ∘ x) y f₁ hf₁.1 (cond_zero P hP.1 x y g₂ g₁ hopt.1.2),
   suff_core P hP.1 (g₂ ∘ x) (g₁ ∘ x) y f₂ hf₂.1 (cond_zero P hP.1 x y g₁ g₂ hopt.1.1)⟩

lemma entropy_fiber_eq {S α β : Type} [Fintype S] [Fintype α] [Fintype β] (P : S → ℝ)
    (X : S → α) (Y : S → β) (H : ∀ ω ω', X ω' = X ω ↔ Y ω' = Y ω) :
    entropy P X = entropy P Y := by
  rw [entropy_eq, entropy_eq]
  congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 2
  unfold law
  congr 1
  ext ω'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact H ω ω'

lemma mi_congr {S α α' β : Type} [Fintype S] [Fintype α] [Fintype α'] [Fintype β]
    (P : S → ℝ) (X : S → α) (X' : S → α') (Y : S → β)
    (H : ∀ ω ω', X ω' = X ω ↔ X' ω' = X' ω) :
    mutualInfo P X Y = mutualInfo P X' Y := by
  unfold mutualInfo
  rw [entropy_fiber_eq P X X' H, entropy_fiber_eq P (fun ω => (X ω, Y ω)) (fun ω => (X' ω, Y ω))]
  intro ω ω'
  simp only [Prod.mk.injEq]
  rw [H ω ω']

lemma mi_comm {S α β : Type} [Fintype S] [Fintype α] [Fintype β] (P : S → ℝ) (X : S → α)
    (Y : S → β) : mutualInfo P X Y = mutualInfo P Y X := by
  unfold mutualInfo
  rw [entropy_comp_eq P (fun ω => (X ω, Y ω)) (fun ω => (Y ω, X ω)) (fun t => (t.2, t.1))
    (fun t => (t.2, t.1)) (fun _ => rfl) (fun _ => rfl)]
  ring

lemma dpi {S V U W : Type} [Fintype S] [Fintype V] [Fintype U] [Fintype W] (P : S → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (v : S → V) (u : S → U) (t : V → W) :
    mutualInfo P (t ∘ v) u ≤ mutualInfo P v u := by
  have N := condMutualInfo_nonneg P hP v u (t ∘ v)
  have q1 : entropy P (fun ω => (v ω, (t ∘ v) ω)) = entropy P v :=
    entropy_comp_eq P _ _ (fun p => p.1) (fun p => (p, t p)) (fun _ => rfl) (fun _ => rfl)
  have q2 : entropy P (fun ω => (u ω, (t ∘ v) ω)) = entropy P (fun ω => ((t ∘ v) ω, u ω)) :=
    entropy_comp_eq P _ _ (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) (fun _ => rfl)
      (fun _ => rfl)
  have q3 : entropy P (fun ω => (v ω, u ω, (t ∘ v) ω)) = entropy P (fun ω => (v ω, u ω)) :=
    entropy_comp_eq P _ _ (fun p => (p.1, p.2.1)) (fun p => (p.1, p.2, t p.1)) (fun _ => rfl)
      (fun _ => rfl)
  simp only [condMutualInfo, mutualInfo] at *
  linarith

lemma exists_rep {X V W : Type} (t : V → W) (v : X → V) :
    ∃ v' : X → V, ∀ ξ ξ', t (v ξ') = t (v ξ) ↔ v' ξ' = v' ξ := by
  let sec : (w : W) → (∃ a, t a = w) → V := fun w h => Classical.choose h
  have hsec : ∀ w h, t (sec w h) = w := fun w h => Classical.choose_spec h
  have hcong : ∀ w1 w2 (h1 : ∃ a, t a = w1) (h2 : ∃ a, t a = w2), w1 = w2 →
      sec w1 h1 = sec w2 h2 := by
    intro w1 w2 h1 h2 e; subst e; rfl
  refine ⟨fun ξ => sec (t (v ξ)) ⟨v ξ, rfl⟩, fun ξ ξ' => ⟨fun e => hcong _ _ _ _ e, fun e => ?_⟩⟩
  have := congrArg t e
  rwa [hsec, hsec] at this

lemma min_core {S V U W Y : Type} [Fintype S] [Fintype V] [Fintype U] [Fintype W] [Fintype Y]
    (P : S → ℝ) (hP : ∀ ω, 0 ≤ P ω) (v : S → V) (u : S → U) (y : S → Y) (t : V → W)
    (v' : S → V) (hv' : ∀ ω ω', (t ∘ v) ω' = (t ∘ v) ω ↔ v' ω' = v' ω)
    (hopt' : mutualInfo P v' y = mutualInfo P v y → mutualInfo P v u ≤ mutualInfo P v' u)
    (ht : mutualInfo P (t ∘ v) y = mutualInfo P v y) :
    mutualInfo P v u = mutualInfo P (t ∘ v) u := by
  have e1 := mi_congr P (t ∘ v) v' y hv'
  have e2 := mi_congr P (t ∘ v) v' u hv'
  have h := hopt' (e1.symm.trans ht)
  have := dpi P hP v u t
  linarith

theorem optimal_views_minimal_representation {S X Y V₁ V₂ Z₁ Z₂ : Type} [Fintype S]
    [Fintype X] [Fintype Y] [Fintype V₁] [Fintype V₂] [Fintype Z₁] [Fintype Z₂]
    (P : S → ℝ) (hP : IsPMF P) (x : S → X) (y : S → Y) (g₁ : X → V₁) (g₂ : X → V₂)
    (hopt : IsOptimalViews P x y g₁ g₂) (f₁ : V₁ → Z₁) (f₂ : V₂ → Z₂)
    (hf₁ : IsMinimalSufficientEncoder P (g₁ ∘ x) (g₂ ∘ x) f₁)
    (hf₂ : IsMinimalSufficientEncoder P (g₂ ∘ x) (g₁ ∘ x) f₂) :
    IsMinimalSufficientStat P (g₁ ∘ x) y f₁ ∧ IsMinimalSufficientStat P (g₂ ∘ x) y f₂ := by
  have hs := optimal_views_sufficient_representation P hP x y g₁ g₂ hopt f₁ f₂ hf₁ hf₂
  refine ⟨⟨hs.1, ?_⟩, ⟨hs.2, ?_⟩⟩
  · intro W _ t ht
    obtain ⟨g', hg'⟩ := exists_rep t g₁
    apply hf₁.2 W t
    refine min_core P hP.1 (g₁ ∘ x) (g₂ ∘ x) y t (g' ∘ x) (fun ω ω' => hg' (x ω) (x ω'))
      (fun h => hopt.2 g' g₂ ⟨h.trans hopt.1.1, hopt.1.2⟩) ht
  · intro W _ t ht
    obtain ⟨g', hg'⟩ := exists_rep t g₂
    apply hf₂.2 W t
    refine min_core P hP.1 (g₂ ∘ x) (g₁ ∘ x) y t (g' ∘ x) (fun ω ω' => hg' (x ω) (x ω'))
      (fun h => ?_) ht
    have := hopt.2 g₁ g' ⟨hopt.1.1, h.trans hopt.1.2⟩
    rw [mi_comm P (g₁ ∘ x), mi_comm P (g₁ ∘ x)] at this
    exact this

end GoodViews
open GoodViews in
theorem solution {S X Y V₁ V₂ Z₁ Z₂ : Type} [Fintype S]
    [Fintype X] [Fintype Y] [Fintype V₁] [Fintype V₂] [Fintype Z₁] [Fintype Z₂]
    (P : S → ℝ) (hP : IsPMF P) (x : S → X) (y : S → Y) (g₁ : X → V₁) (g₂ : X → V₂)
    (hopt : IsOptimalViews P x y g₁ g₂) (f₁ : V₁ → Z₁) (f₂ : V₂ → Z₂)
    (hf₁ : IsMinimalSufficientEncoder P (g₁ ∘ x) (g₂ ∘ x) f₁)
    (hf₂ : IsMinimalSufficientEncoder P (g₂ ∘ x) (g₁ ∘ x) f₂) :
    IsMinimalSufficientStat P (g₁ ∘ x) y f₁ ∧ IsMinimalSufficientStat P (g₂ ∘ x) y f₂ :=
  optimal_views_minimal_representation P hP x y g₁ g₂ hopt f₁ f₂ hf₁ hf₂
