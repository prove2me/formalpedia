-- Prove2me | solution 1 for GlobalTheory.isolate_abstract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:40.297097+00:00
-- url     : https://prove2.me/submissions/1454bcfd-82c4-4813-a63b-449bd142ac57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsolateAbstract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] (Γ G : AddSubgroup X) (V : Type) [AddCommGroup V] [Module ℂ V] (T : X → V →ₗ[ℂ] V) (W : Set V) (β : X → X → ℂ) (a : X → ℂ) (χ : X → X → ℂ), Γ ≤ G → (∀ v, T 0 v = v) → (∀ x y v, T x (T y v) = β x y • T (x + y) v) → (∀ x y, β x y ≠ 0) → (∀ γ ∈ Γ, a γ ≠ 0 ∧ ∀ v ∈ W, T γ v = a γ • v) → (∀ γ ∈ Γ, ∀ x v, T γ (T x v) = χ x γ • T x (T γ v)) → (∀ x, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, χ (x + γ') γ = χ x γ) → (∀ x ∈ G, ∀ y ∈ G, x - y ∉ Γ → ∃ γ ∈ Γ, χ x γ ≠ χ y γ) → ∀ (J : Finset X) (c : X → ℂ), (∀ x ∈ J, x ∈ G) → (∀ v ∈ W, ∑ x ∈ J, c x • T x v = 0) ∨ ∃ κ : X →₀ ℂ, (∀ y ∈ κ.support, y ∈ G) ∧ ∀ v ∈ W, ∑ y ∈ κ.support, κ y • T y (∑ x ∈ J, c x • T x v) = v := by
  intro X _ Γ G V _ _ T W β a χ hΓG hT0 hTT hβ ha hχ hχc hsep J c hJ
  classical
  obtain ⟨A, hA⟩ : ∃ A : Submodule ℂ (V →ₗ[ℂ] V), A = Submodule.span ℂ (T '' (G : Set X)) := ⟨_, rfl⟩
  have hTA : ∀ y ∈ G, T y ∈ A := fun y hy => hA ▸ Submodule.subset_span ⟨y, hy, rfl⟩
  have hmulT : ∀ y ∈ G, ∀ g ∈ A, T y * g ∈ A := by
    intro y hy g hg
    rw [hA] at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨z, hz, rfl⟩ := hg
      have e : T y * T z = β y z • T (y + z) := by ext v; simp [hTT]
      rw [e]; exact A.smul_mem _ (hTA _ (G.add_mem hy hz))
    | zero => simp
    | add f g _ _ hf hg => rw [mul_add]; exact A.add_mem hf hg
    | smul r f _ hf => rw [mul_smul_comm]; exact A.smul_mem r hf
  have hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A := by
    intro f hf g hg
    rw [hA] at hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨y, hy, rfl⟩ := hf; exact hmulT y hy g hg
    | zero => simp
    | add f f' _ _ h h' => rw [add_mul]; exact A.add_mem h h'
    | smul r f _ h => rw [smul_mul_assoc]; exact A.smul_mem r h
  have hone : (1 : V →ₗ[ℂ] V) ∈ A := by
    have e : (1 : V →ₗ[ℂ] V) = T 0 := by ext v; simp [hT0]
    rw [e]; exact hTA 0 G.zero_mem
  have hκ : ∀ L ∈ A, ∃ κ : X →₀ ℂ, (∀ y ∈ κ.support, y ∈ G) ∧ ∀ u, ∑ y ∈ κ.support, κ y • T y u = L u := by
    intro L hL
    rw [hA, Finsupp.mem_span_image_iff_linearCombination] at hL
    obtain ⟨l, hl, rfl⟩ := hL
    refine ⟨l, fun y hy => (Finsupp.mem_supported _ _).1 hl hy, fun u => ?_⟩
    simp [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  have hshift : ∀ x0 x, x - x0 ∈ Γ → ∀ v ∈ W, T x v = ((β x0 (x - x0))⁻¹ * a (x - x0)) • T x0 v := by
    intro x0 x h v hv
    have h1 := hTT x0 (x - x0) v
    have e : x0 + (x - x0) = x := by abel
    rw [(ha _ h).2 v hv, map_smul, e] at h1
    rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ (hβ _ _), one_smul]
  have hcls : ∀ x0 (c : X → ℂ), ∀ v ∈ W, ∑ x ∈ J, (if x - x0 ∈ Γ then c x else 0) • T x v
      = (∑ x ∈ J, if x - x0 ∈ Γ then c x * ((β x0 (x - x0))⁻¹ * a (x - x0)) else 0) • T x0 v := by
    intro x0 c v hv
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [mul_smul, ← hshift x0 x h v hv]
    · simp
  have hQ : ∀ γ ∈ Γ, ∀ k : ℂ, ∀ c : X → ℂ, ∀ v ∈ W,
      ((a γ)⁻¹ • T γ - k • (1 : V →ₗ[ℂ] V)) (∑ x ∈ J, c x • T x v) = ∑ x ∈ J, (c x * (χ x γ - k)) • T x v := by
    intro γ hγ k c v hv
    have hb : ∀ x, T γ (T x v) = (χ x γ * a γ) • T x v := by
      intro x; rw [hχ γ hγ x v, (ha γ hγ).2 v hv, map_smul, smul_smul]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sum, map_smul, hb,
      Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [smul_smul, ← sub_smul]
    congr 1
    have := (ha γ hγ).1
    field_simp
  have hQA : ∀ γ ∈ Γ, ∀ k : ℂ, ((a γ)⁻¹ • T γ - k • (1 : V →ₗ[ℂ] V)) ∈ A := fun γ hγ k =>
    A.sub_mem (A.smul_mem _ (hTA γ (hΓG hγ))) (A.smul_mem _ hone)
  have hproj : ∀ x0 ∈ G, ∀ n : ℕ, ∀ c : X → ℂ, (J.filter (fun x => c x ≠ 0 ∧ x - x0 ∉ Γ)).card = n →
      ∃ L ∈ A, ∃ s : ℂ, s ≠ 0 ∧ ∀ v ∈ W,
        L (∑ x ∈ J, c x • T x v) = s • ∑ x ∈ J, (if x - x0 ∈ Γ then c x else 0) • T x v := by
    intro x0 hx0 n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro c hn
    by_cases hS : ∃ x1 ∈ J, c x1 ≠ 0 ∧ x1 - x0 ∉ Γ
    · obtain ⟨x1, hx1J, hcx1, hx1⟩ := hS
      obtain ⟨γ, hγ, hne⟩ := hsep x1 (hJ x1 hx1J) x0 hx0 hx1
      obtain ⟨c', hc'⟩ : ∃ c' : X → ℂ, c' = fun x => c x * (χ x γ - χ x1 γ) := ⟨_, rfl⟩
      have hsub : J.filter (fun x => c' x ≠ 0 ∧ x - x0 ∉ Γ) ⊂ J.filter (fun x => c x ≠ 0 ∧ x - x0 ∉ Γ) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨x1, by simp [hx1J, hcx1, hx1], ?_⟩
          simp [hc']
        · intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, fun h => hx.2.1 (by simp [hc', h]), hx.2.2⟩
      obtain ⟨L', hL', s', hs', hL'eq⟩ := ih _ (hn ▸ Finset.card_lt_card hsub) c' rfl
      refine ⟨L' * ((a γ)⁻¹ • T γ - χ x1 γ • (1 : V →ₗ[ℂ] V)), hmul _ hL' _ (hQA γ hγ _),
        s' * (χ x0 γ - χ x1 γ), mul_ne_zero hs' (sub_ne_zero.2 (Ne.symm hne)), fun v hv => ?_⟩
      rw [Module.End.mul_apply, hQ γ hγ _ c v hv,
        show (∑ x ∈ J, (c x * (χ x γ - χ x1 γ)) • T x v) = ∑ x ∈ J, c' x • T x v by rw [hc'],
        hL'eq v hv, mul_smul]
      congr 1
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with h
      · have hχx : χ x γ = χ x0 γ := by simpa using hχc x0 γ hγ (x - x0) h
        simp only [hc', smul_smul, hχx, mul_comm]
      · simp
    · push_neg at hS
      refine ⟨1, hone, 1, one_ne_zero, fun v hv => ?_⟩
      rw [Module.End.one_apply, one_smul]
      refine Finset.sum_congr rfl fun x hx => ?_
      split_ifs with h
      · rfl
      · by_cases hc : c x = 0
        · simp [hc]
        · exact absurd (hS x hx hc) h
  have main : ∀ n : ℕ, ∀ c : X → ℂ, (J.filter (fun x => c x ≠ 0)).card = n →
      (∀ v ∈ W, ∑ x ∈ J, c x • T x v = 0) ∨ ∃ L ∈ A, ∀ v ∈ W, L (∑ x ∈ J, c x • T x v) = v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro c hn
    by_cases hS : ∃ x0 ∈ J, c x0 ≠ 0
    · obtain ⟨x0, hx0J, hcx0⟩ := hS
      have hx0 := hJ x0 hx0J
      obtain ⟨d, hd⟩ : ∃ d : ℂ, d = ∑ x ∈ J, if x - x0 ∈ Γ then c x * ((β x0 (x - x0))⁻¹ * a (x - x0)) else 0 :=
        ⟨_, rfl⟩
      by_cases hd0 : d = 0
      · obtain ⟨c'', hc''⟩ : ∃ c'' : X → ℂ, c'' = fun x => if x - x0 ∈ Γ then 0 else c x := ⟨_, rfl⟩
        have hsub : J.filter (fun x => c'' x ≠ 0) ⊂ J.filter (fun x => c x ≠ 0) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨x0, by simp [hx0J, hcx0], ?_⟩
            simp [hc'']
          · intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            refine ⟨hx.1, fun h => hx.2 ?_⟩
            simp [hc'', h]
        have heq : ∀ v ∈ W, ∑ x ∈ J, c x • T x v = ∑ x ∈ J, c'' x • T x v := by
          intro v hv
          have h1 := hcls x0 c v hv
          rw [← hd, hd0, zero_smul] at h1
          calc ∑ x ∈ J, c x • T x v
              = ∑ x ∈ J, ((if x - x0 ∈ Γ then c x else 0) • T x v + c'' x • T x v) :=
                Finset.sum_congr rfl fun x _ => by simp only [hc'']; split_ifs <;> simp
            _ = ∑ x ∈ J, c'' x • T x v := by rw [Finset.sum_add_distrib, h1, zero_add]
        rcases ih _ (hn ▸ Finset.card_lt_card hsub) c'' rfl with h | ⟨L, hL, hLeq⟩
        · exact Or.inl fun v hv => by rw [heq v hv]; exact h v hv
        · exact Or.inr ⟨L, hL, fun v hv => by rw [heq v hv]; exact hLeq v hv⟩
      · obtain ⟨L, hL, s, hs, hLeq⟩ := hproj x0 hx0 _ c rfl
        refine Or.inr ⟨(((s * d) * β (-x0) x0)⁻¹ • T (-x0)) * L,
          hmul _ (A.smul_mem _ (hTA _ (G.neg_mem hx0))) _ hL, fun v hv => ?_⟩
        rw [Module.End.mul_apply, LinearMap.smul_apply, hLeq v hv, hcls x0 c v hv, ← hd, map_smul, map_smul,
          hTT, neg_add_cancel, hT0, smul_smul, smul_smul, smul_smul]
        have hβ' := hβ (-x0) x0
        have e : ((s * d) * β (-x0) x0)⁻¹ * s * d * β (-x0) x0 = 1 := by
          field_simp
        rw [e, one_smul]
    · push_neg at hS
      exact Or.inl fun v _ => Finset.sum_eq_zero fun x hx => by simp [hS x hx]
  rcases main _ c rfl with h | ⟨L, hL, hLeq⟩
  · exact Or.inl h
  · obtain ⟨κ, hκG, hκeq⟩ := hκ L hL
    exact Or.inr ⟨κ, hκG, fun v hv => by rw [hκeq, hLeq v hv]⟩
end GlobalTheory
