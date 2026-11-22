-- Prove2me | solution 1 for HardyCausaloid.eq37_value_ratio_of_lengths
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T20:09:50.478594+00:00
-- url     : https://prove2.me/submissions/c9c2b833-3256-4264-8f3a-3d831c26a89e

import Theorems.Thm_HardyCausaloid_eq35_conditional_ratio
import Theorems.Thm_HardyCausaloid_fiducial_spanning_states

namespace HardyCausaloid
variable {X : Type*} {Setting : X → Type*} {Outcome : (x : X) → Setting x → Type*}
  [DecidableEq X]

private theorem regional_state_span (M : Model Setting Outcome) (C : Causaloid Setting Outcome)
    (O : Finset X)
    (h : Submodule.span ℝ (Set.range (stateVec (regionTable M O) (C.fidSet O))) = ⊤) :
    Submodule.span ℝ (Set.range (C.state M O)) = ⊤ := by
  let e : C.ΩC O ≃ C.fidSet O := Finset.equivMap ⟨C.embed O, C.embed_injective O⟩ _
  let f : (C.fidSet O → ℝ) →ₗ[ℝ] (C.ΩC O → ℝ) := LinearMap.pi fun i => LinearMap.proj (e i)
  have hf : Function.Surjective f := by
    intro w
    refine ⟨fun i => w (e.symm i), funext fun i => ?_⟩
    change w (e.symm (e i)) = w i
    simp
  change Submodule.span ℝ (Set.range (f ∘ stateVec (regionTable M O) (C.fidSet O))) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

end HardyCausaloid
namespace HardyCausaloid

private theorem states_separate {ι S : Type*} [Fintype ι] (p : S → ι → ℝ)
    (hs : Submodule.span ℝ (Set.range p) = ⊤) {u v : ι → ℝ}
    (h : ∀ s, u ⬝ᵥ p s = v ⬝ᵥ p s) : u = v := by
  apply dotProduct_eq
  intro x
  have hx : x ∈ Submodule.span ℝ (Set.range p) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨s, rfl⟩ := hx; exact h s
  | zero => simp
  | add x y _ _ hx hy => simp only [dotProduct_add, hx, hy]
  | smul c x _ hx => simp only [dotProduct_smul, hx]

private theorem length_pos {ι : Type*} [Fintype ι] {v : ι → ℝ} (h : v ≠ 0) :
    0 < euclidLength v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  apply Real.sqrt_pos.mpr
  exact (sq_pos_of_ne_zero hi).trans_le (Finset.single_le_sum
    (f := fun j => (v j)^2) (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

private theorem length_smul {ι : Type*} [Fintype ι] (v : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    euclidLength (c • v) = c * euclidLength v := by
  simp only [euclidLength, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

end HardyCausaloid

open HardyCausaloid
theorem solution {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    (C : Causaloid Setting Outcome) (hC : IsCausaloidOf C M)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂) (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x)) :
    (∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c → condA C α₁ F₂ Y₂ = c • condB C α₁ F₂) ∧
    (condB C α₁ F₂ ≠ 0 → ∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c →
      c = euclidLength (condA C α₁ F₂ Y₂) / euclidLength (condB C α₁ F₂)) ∧
    (condB C α₁ F₂ = 0 ↔ ∀ s, condDen M α₁ F₂ s = 0) := by
  have h35 := eq35_conditional_ratio M C hC hO α₁ F₂ Y₂
  have hsFid := (fiducial_spanning_states _ _ (hC.region_fiducial (O₁ ∪ O₂))).1
  let p := C.state M (O₁ ∪ O₂)
  let a := condA C α₁ F₂ Y₂
  let b := condB C α₁ F₂
  have hp := regional_state_span M C (O₁ ∪ O₂) hsFid
  obtain ⟨_, hs, hn, hd⟩ := h35
  have nonneg s (β : ∀ x : O₂, Outcome x.val (F₂ x)) :
      0 ≤ regionTable M (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β)) s := M.prob_nonneg _ _
  have num_le s : condNum M α₁ F₂ Y₂ s ≤ condDen M α₁ F₂ s :=
    (hs s).le_tsum Y₂ (fun β _ => nonneg s β)
  have zero : b = 0 ↔ ∀ s, condDen M α₁ F₂ s = 0 := by
    constructor
    · intro h s
      rw [hd]
      change b ⬝ᵥ p s = 0
      simp [h]
    · intro h
      apply states_separate p hp
      intro s
      simpa only [zero_dotProduct] using (hd s).symm.trans (h s)
  have proportional c (h : IsCondValue M α₁ F₂ Y₂ c) : a = c • b := by
    apply states_separate p hp
    intro s
    rw [smul_dotProduct]
    change condA C α₁ F₂ Y₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s =
      c * (condB C α₁ F₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s)
    rw [← hn, ← hd]
    by_cases hz : condDen M α₁ F₂ s = 0
    · have hzero := le_antisymm ((num_le s).trans hz.le) (nonneg s Y₂)
      rw [hz, mul_zero, hzero]
    · exact (div_eq_iff hz).mp (h s hz)
  refine ⟨proportional, ?_, zero⟩
  intro hb c h
  obtain ⟨s, hden⟩ := not_forall.mp (fun h => hb (zero.mpr h))
  have hc : 0 ≤ c := by
    rw [← h s hden]
    exact div_nonneg (nonneg s Y₂) ((nonneg s Y₂).trans (num_le s))
  change c = euclidLength a / euclidLength b
  rw [proportional c h, length_smul _ _ hc]
  exact (mul_div_cancel_right₀ _ (length_pos hb).ne').symm
