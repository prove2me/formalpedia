-- Prove2me | solution 1 for MasulloGRH.nuclear_prod
-- status  : ACCEPTED   (prove)
-- author  : @koffie
-- created : 2026-11-20T22:56:14.988183+00:00
-- url     : https://prove2.me/submissions/b91ed901-6149-4f58-83f5-535a38c4c1fd

import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination
import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination

set_option autoImplicit false

open MasulloGRH TensorProduct Topology

universe u

namespace NuclearProdAux

/-- quasi-nuclear domination of a seminorm -/
def Dom {X : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] (p : Seminorm ℂ X) :
    Prop :=
  ∃ (q : Seminorm ℂ X) (f : ℕ → StrongDual ℂ X) (c : ℕ → ℝ),
    Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
    ∀ x, p x ≤ ∑' n, c n * ‖f n x‖

variable {X Y : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

lemma dom_mono {p p' : Seminorm ℂ X} (h : p ≤ p') (hp' : Dom p') : Dom p := by
  obtain ⟨q, f, c, hq, hc0, hcs, hfq, hd⟩ := hp'
  exact ⟨q, f, c, hq, hc0, hcs, hfq, fun x => (h x).trans (hd x)⟩

lemma dom_comp (L : X →L[ℂ] Y) {r : Seminorm ℂ Y} (hr : Dom r) :
    Dom (r.comp (L : X →ₗ[ℂ] Y)) := by
  obtain ⟨q, f, c, hq, hc0, hcs, hfq, hd⟩ := hr
  exact ⟨q.comp (L : X →ₗ[ℂ] Y), fun n => (f n).comp L, c, hq.comp L.continuous, hc0, hcs,
    fun n x => hfq n (L x), fun x => hd (L x)⟩

/-- interleaving two sequences -/
def il {α : Type*} (a b : ℕ → α) : ℕ → α := fun k => if k % 2 = 0 then a (k / 2) else b (k / 2)

lemma il_even {α : Type*} (a b : ℕ → α) (k : ℕ) : il a b (2 * k) = a k := by
  simp [il]

lemma il_odd {α : Type*} (a b : ℕ → α) (k : ℕ) : il a b (2 * k + 1) = b k := by
  simp only [il]
  rw [if_neg (by omega)]
  congr 1; omega

lemma il_hasSum {a b : ℕ → ℝ} {A B : ℝ} (ha : HasSum a A) (hb : HasSum b B) :
    HasSum (il a b) (A + B) := by
  apply HasSum.even_add_odd
  · simpa [il_even] using ha
  · simpa [il_odd] using hb

lemma dom_add {p₁ p₂ : Seminorm ℂ X} (h₁ : Dom p₁) (h₂ : Dom p₂) : Dom (p₁ + p₂) := by
  obtain ⟨q₁, f₁, c₁, hq₁, hc₁, hs₁, hf₁, hd₁⟩ := h₁
  obtain ⟨q₂, f₂, c₂, hq₂, hc₂, hs₂, hf₂, hd₂⟩ := h₂
  refine ⟨q₁ + q₂, il f₁ f₂, il c₁ c₂, ?_, ?_, ?_, ?_, ?_⟩
  · show Continuous fun x => q₁ x + q₂ x
    exact hq₁.add hq₂
  · intro n; unfold il; split_ifs <;> simp [hc₁, hc₂]
  · exact (il_hasSum hs₁.hasSum hs₂.hasSum).summable
  · intro n x
    unfold il
    split_ifs
    · exact (hf₁ _ x).trans (le_add_of_nonneg_right (apply_nonneg _ _))
    · exact (hf₂ _ x).trans (le_add_of_nonneg_left (apply_nonneg _ _))
  · intro x
    have s₁ : Summable fun n => c₁ n * ‖f₁ n x‖ :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (hc₁ n) (norm_nonneg _))
        (fun n => mul_le_mul_of_nonneg_left (hf₁ n x) (hc₁ n)) (hs₁.mul_right (q₁ x))
    have s₂ : Summable fun n => c₂ n * ‖f₂ n x‖ :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (hc₂ n) (norm_nonneg _))
        (fun n => mul_le_mul_of_nonneg_left (hf₂ n x) (hc₂ n)) (hs₂.mul_right (q₂ x))
    have hsum : HasSum (fun n => il c₁ c₂ n * ‖il f₁ f₂ n x‖)
        ((∑' n, c₁ n * ‖f₁ n x‖) + ∑' n, c₂ n * ‖f₂ n x‖) := by
      have := il_hasSum s₁.hasSum s₂.hasSum
      convert this using 1
      funext k; unfold il; split_ifs <;> rfl
    rw [hsum.tsum_eq, Seminorm.add_apply]
    exact add_le_add (hd₁ x) (hd₂ x)

end NuclearProdAux

open NuclearProdAux

theorem solution (E G : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] (hE : IsNuclear E) (hG : IsNuclear G) :
    IsNuclear (E × G) := by
  obtain ⟨⟨ιE, hιE, pE, hpE⟩, hT2E⟩ := hE.1
  obtain ⟨⟨ιG, hιG, pG, hpG⟩, hT2G⟩ := hG.1
  have : IsTopologicalAddGroup E := hpE.topologicalAddGroup
  have : IsTopologicalAddGroup G := hpG.topologicalAddGroup
  have : PolynormableSpace ℂ E := hpE.toPolynormableSpace
  have : PolynormableSpace ℂ G := hpG.toPolynormableSpace
  have hP : WithSeminorms (fun p : {p : Seminorm ℂ (E × G) // Continuous p} ↦ p.1) :=
    PolynormableSpace.withSeminorms ℂ (E × G)
  apply nuclear_of_quasinuclear_domination (E × G)
    ⟨⟨_, ⟨⟨0, continuous_const⟩⟩, _, hP⟩, inferInstance⟩
  intro p hp
  -- split `p` along the two factors
  set p₁ : Seminorm ℂ E := p.comp (LinearMap.inl ℂ E G)
  set p₂ : Seminorm ℂ G := p.comp (LinearMap.inr ℂ E G)
  have hp₁ : Continuous p₁ := hp.comp (continuous_id.prodMk continuous_const)
  have hp₂ : Continuous p₂ := hp.comp (continuous_const.prodMk continuous_id)
  have hle : p ≤ p₁.comp (ContinuousLinearMap.fst ℂ E G : E × G →ₗ[ℂ] E) +
      p₂.comp (ContinuousLinearMap.snd ℂ E G : E × G →ₗ[ℂ] G) := by
    intro x
    have hx : x = (x.1, 0) + (0, x.2) := by simp
    calc p x = p ((x.1, 0) + (0, x.2)) := by rw [← hx]
      _ ≤ p (x.1, 0) + p (0, x.2) := map_add_le_add p _ _
      _ = _ := rfl
  exact dom_mono hle (dom_add
    (dom_comp (ContinuousLinearMap.fst ℂ E G) (nuclear_quasinuclear_domination E hE p₁ hp₁))
    (dom_comp (ContinuousLinearMap.snd ℂ E G) (nuclear_quasinuclear_domination G hG p₂ hp₂)))
