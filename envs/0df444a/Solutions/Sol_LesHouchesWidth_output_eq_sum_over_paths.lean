-- Prove2me | solution 1 for LesHouchesWidth.output_eq_sum_over_paths
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:22:09.774035+00:00
-- url     : https://prove2.me/submissions/c8315504-bfd2-475b-bb31-521b6eed77b5

import Mathlib
import Definitions.Def_LesHouchesWidth_ReLUNet

open MeasureTheory ProbabilityTheory
open LesHouchesWidth

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

section Paths
variable {n : ℕ → ℕ} {L : ℕ}

noncomputable def W5_LesHouchesWidth_wv (ω : Weights n L) (ℓ a b : ℕ) : ℝ :=
  if h : a < n (ℓ + 1) ∧ b < n ℓ then weight ω ℓ ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

theorem W5_LesHouchesWidth_weight_eq (ω : Weights n L) (ℓ : ℕ) (i : Fin (n (ℓ + 1)))
    (j : Fin (n ℓ)) : weight ω ℓ i j = W5_LesHouchesWidth_wv ω ℓ i.val j.val := by
  simp [W5_LesHouchesWidth_wv, i.isLt, j.isLt]

noncomputable def W5_LesHouchesWidth_xv (x : Fin (n 0) → ℝ) (a : ℕ) : ℝ :=
  if h : a < n 0 then x ⟨a, h⟩ else 0

noncomputable def W5_LesHouchesWidth_av (ω : Weights n L) (x : Fin (n 0) → ℝ) (ℓ a : ℕ) : ℝ :=
  if h : a < n ℓ then (if 0 < netZ ω x ℓ ⟨a, h⟩ then 1 else 0) else 0

theorem W5_LesHouchesWidth_av_eq (ω : Weights n L) (x : Fin (n 0) → ℝ) (ℓ : ℕ) (a : Fin (n ℓ)) :
    W5_LesHouchesWidth_av ω x ℓ a.val = if 0 < netZ ω x ℓ a then 1 else 0 := by
  simp [W5_LesHouchesWidth_av, a.isLt]

/-- Sum over partial paths through layers `0, …, m+1` ending at neuron `i`. -/
noncomputable def W5_LesHouchesWidth_Q (ω : Weights n L) (x : Fin (n 0) → ℝ) (m i : ℕ) : ℝ :=
  ∑ γ : ((k : Fin (m + 2)) → Fin (n k.val)),
    if (γ (Fin.last (m + 1))).val = i then
      W5_LesHouchesWidth_xv x (γ 0).val *
        (∏ k : Fin (m + 1), W5_LesHouchesWidth_wv ω k.val (γ k.succ).val (γ k.castSucc).val) *
        (∏ k : Fin m, W5_LesHouchesWidth_av ω x (k.val + 1) (γ ⟨k.val + 1, by omega⟩).val)
    else 0

theorem W5_LesHouchesWidth_relu (t : ℝ) : relu t = t * (if 0 < t then 1 else 0) := by
  unfold relu
  split_ifs with h
  · rw [max_eq_left h.le, mul_one]
  · rw [max_eq_right (not_lt.mp h), mul_zero]

theorem W5_LesHouchesWidth_sum_snoc (m : ℕ) (F : ((k : Fin (m + 3)) → Fin (n k.val)) → ℝ) :
    ∑ γ, F γ = ∑ c : Fin (n (m + 2)), ∑ γ' : ((k : Fin (m + 2)) → Fin (n k.val)),
      F (Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c) := by
  exact ((Fin.snocEquiv (fun k : Fin (m + 3) => Fin (n k.val))).sum_comp F).symm.trans
    (Fintype.sum_prod_type _)

theorem W5_LesHouchesWidth_base (ω : Weights n L) (x : Fin (n 0) → ℝ) (i : Fin (n 1)) :
    netZ ω x 1 i = W5_LesHouchesWidth_Q ω x 0 i.val := by
  have hL : netZ ω x 1 i = ∑ a : Fin (n 0), ∑ b : Fin (n 1),
      if b = i then x a * weight ω 0 i a else 0 := by
    rw [show netZ ω x 1 i = ∑ j, weight ω 0 i j *
      (if 0 = 0 then netZ ω x 0 j else relu (netZ ω x 0 j)) from rfl]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos rfl]
    exact mul_comm _ _
  have hsplit : ∀ F : ((k : Fin (0 + 2)) → Fin (n k.val)) → ℝ, ∑ γ, F γ =
      ∑ a : Fin (n 0), ∑ b : Fin (n 1),
        F ((piFinTwoEquiv (fun k : Fin 2 => Fin (n k.val))).symm (a, b)) :=
    fun F => ((piFinTwoEquiv (fun k : Fin 2 => Fin (n k.val))).symm.sum_comp F).symm.trans
      (Fintype.sum_prod_type _)
  rw [hL]
  unfold W5_LesHouchesWidth_Q
  rw [hsplit]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  have v1 : (((piFinTwoEquiv (fun k : Fin 2 => Fin (n k.val))).symm (a, b))
      (Fin.last (0 + 1))).val = b.val := rfl
  have v2 : (((piFinTwoEquiv (fun k : Fin 2 => Fin (n k.val))).symm (a, b)) 0).val
      = a.val := rfl
  have v3 : (((piFinTwoEquiv (fun k : Fin 2 => Fin (n k.val))).symm (a, b))
      (Fin.succ (0 : Fin (0 + 1)))).val = b.val := rfl
  have v4 : (((piFinTwoEquiv (fun k : Fin 2 => Fin (n k.val))).symm (a, b))
      (Fin.castSucc (0 : Fin (0 + 1)))).val = a.val := rfl
  have v5 : ((0 : Fin (0 + 1)) : ℕ) = 0 := rfl
  rw [v1, v2, v3, v4, v5]
  split_ifs with h1 h2 h2
  · subst h1
    rw [W5_LesHouchesWidth_weight_eq]
    simp only [W5_LesHouchesWidth_xv, dif_pos a.isLt]
  · exact absurd (congrArg Fin.val h1) h2
  · exact absurd (Fin.ext h2) h1
  · rfl

theorem W5_LesHouchesWidth_step (ω : Weights n L) (x : Fin (n 0) → ℝ) (m : ℕ)
    (ih : ∀ j : Fin (n (m + 1)), netZ ω x (m + 1) j = W5_LesHouchesWidth_Q ω x m j.val)
    (i : Fin (n (m + 2))) :
    netZ ω x (m + 2) i = W5_LesHouchesWidth_Q ω x (m + 1) i.val := by
  -- left side
  have hL : netZ ω x (m + 2) i = ∑ j : Fin (n (m + 1)),
      W5_LesHouchesWidth_wv ω (m + 1) i.val j.val * W5_LesHouchesWidth_av ω x (m + 1) j.val *
        W5_LesHouchesWidth_Q ω x m j.val := by
    rw [show netZ ω x (m + 2) i = ∑ j, weight ω (m + 1) i j *
      (if m + 1 = 0 then netZ ω x (m + 1) j else relu (netZ ω x (m + 1) j)) from rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_neg (Nat.succ_ne_zero m), W5_LesHouchesWidth_relu, W5_LesHouchesWidth_weight_eq,
      W5_LesHouchesWidth_av_eq, ih j]
    ring
  rw [hL]
  conv_rhs => rw [W5_LesHouchesWidth_Q]
  rw [W5_LesHouchesWidth_sum_snoc]
  -- evaluations of snoc
  have eW : ∀ (γ' : (k : Fin (m + 2)) → Fin (n k.val)) (c : Fin (n (m + 2))),
      ∏ k : Fin (m + 2), W5_LesHouchesWidth_wv ω k.val
        ((Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c) k.succ).val
        ((Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c) k.castSucc).val =
      (∏ k : Fin (m + 1), W5_LesHouchesWidth_wv ω k.val (γ' k.succ).val (γ' k.castSucc).val) *
        W5_LesHouchesWidth_wv ω (m + 1) c.val (γ' (Fin.last (m + 1))).val := by
    intro γ' c
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      have a1 : ((Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c)
          (Fin.castSucc k).succ).val = (γ' k.succ).val := by
        rw [Fin.succ_castSucc, Fin.snoc_castSucc]
      have a2 : ((Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c)
          (Fin.castSucc k).castSucc).val = (γ' k.castSucc).val := by
        rw [Fin.snoc_castSucc]
      rw [a1, a2]
      rfl
    · have a1 : ((Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c)
          (Fin.last (m + 1)).succ).val = c.val := by
        rw [Fin.succ_last, Fin.snoc_last]
      have a2 : ((Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c)
          (Fin.last (m + 1)).castSucc).val = (γ' (Fin.last (m + 1))).val := by
        rw [Fin.snoc_castSucc]
      rw [a1, a2]
      rfl
  have eA : ∀ (γ' : (k : Fin (m + 2)) → Fin (n k.val)) (c : Fin (n (m + 2))),
      ∏ k : Fin (m + 1), W5_LesHouchesWidth_av ω x (k.val + 1)
        ((Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c) ⟨k.val + 1, by omega⟩).val =
      (∏ k : Fin m, W5_LesHouchesWidth_av ω x (k.val + 1) (γ' ⟨k.val + 1, by omega⟩).val) *
        W5_LesHouchesWidth_av ω x (m + 1) (γ' (Fin.last (m + 1))).val := by
    intro γ' c
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      have a1 : ((Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c)
          ⟨(Fin.castSucc k).val + 1, by omega⟩).val = (γ' ⟨k.val + 1, by omega⟩).val := by
        rw [show (⟨(Fin.castSucc k).val + 1, by omega⟩ : Fin (m + 3)) =
          Fin.castSucc ⟨k.val + 1, by omega⟩ from Fin.ext rfl, Fin.snoc_castSucc]
      rw [a1]
      rfl
    · have a1 : ((Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c)
          ⟨(Fin.last m).val + 1, by omega⟩).val = (γ' (Fin.last (m + 1))).val := by
        rw [show (⟨(Fin.last m).val + 1, by omega⟩ : Fin (m + 3)) =
          Fin.castSucc (Fin.last (m + 1)) from Fin.ext rfl, Fin.snoc_castSucc]
      rw [a1]
      rfl
  have e0 : ∀ (γ' : (k : Fin (m + 2)) → Fin (n k.val)) (c : Fin (n (m + 2))),
      ((Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c) 0).val = (γ' 0).val := by
    intro γ' c
    rw [show (0 : Fin (m + 3)) = Fin.castSucc (0 : Fin (m + 2)) from rfl, Fin.snoc_castSucc]
  have eL : ∀ (γ' : (k : Fin (m + 2)) → Fin (n k.val)) (c : Fin (n (m + 2))),
      ((Fin.snoc (α := fun k : Fin (m + 3) => Fin (n k.val)) γ' c) (Fin.last (m + 2))).val =
        c.val := by
    intro γ' c
    rw [Fin.snoc_last]
  simp only [eW, eA, e0, eL]
  -- collapse the sum over the last neuron
  have hc : ∀ γ' : (k : Fin (m + 2)) → Fin (n k.val),
      ∑ c : Fin (n (m + 2)), (if c.val = i.val then
        W5_LesHouchesWidth_xv x (γ' 0).val *
          ((∏ k : Fin (m + 1), W5_LesHouchesWidth_wv ω k.val (γ' k.succ).val (γ' k.castSucc).val) *
            W5_LesHouchesWidth_wv ω (m + 1) c.val (γ' (Fin.last (m + 1))).val) *
          ((∏ k : Fin m, W5_LesHouchesWidth_av ω x (k.val + 1) (γ' ⟨k.val + 1, by omega⟩).val) *
            W5_LesHouchesWidth_av ω x (m + 1) (γ' (Fin.last (m + 1))).val) else 0) =
      W5_LesHouchesWidth_xv x (γ' 0).val *
          ((∏ k : Fin (m + 1), W5_LesHouchesWidth_wv ω k.val (γ' k.succ).val (γ' k.castSucc).val) *
            W5_LesHouchesWidth_wv ω (m + 1) i.val (γ' (Fin.last (m + 1))).val) *
          ((∏ k : Fin m, W5_LesHouchesWidth_av ω x (k.val + 1) (γ' ⟨k.val + 1, by omega⟩).val) *
            W5_LesHouchesWidth_av ω x (m + 1) (γ' (Fin.last (m + 1))).val) := by
    intro γ'
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hci
      rw [if_neg (fun h => hci (Fin.ext h))]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_comm]
  simp only [hc]
  -- right side regrouped
  have hR : ∀ j : Fin (n (m + 1)),
      W5_LesHouchesWidth_wv ω (m + 1) i.val j.val * W5_LesHouchesWidth_av ω x (m + 1) j.val *
        W5_LesHouchesWidth_Q ω x m j.val =
      ∑ γ' : ((k : Fin (m + 2)) → Fin (n k.val)), if γ' (Fin.last (m + 1)) = j then
        W5_LesHouchesWidth_xv x (γ' 0).val *
          ((∏ k : Fin (m + 1), W5_LesHouchesWidth_wv ω k.val (γ' k.succ).val (γ' k.castSucc).val) *
            W5_LesHouchesWidth_wv ω (m + 1) i.val (γ' (Fin.last (m + 1))).val) *
          ((∏ k : Fin m, W5_LesHouchesWidth_av ω x (k.val + 1) (γ' ⟨k.val + 1, by omega⟩).val) *
            W5_LesHouchesWidth_av ω x (m + 1) (γ' (Fin.last (m + 1))).val) else 0 := by
    intro j
    unfold W5_LesHouchesWidth_Q
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ' _ => ?_
    by_cases h : γ' (Fin.last (m + 1)) = j
    · rw [if_pos (congrArg Fin.val h), if_pos h, h]
      ring
    · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl fun j _ => hR j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ' _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem W5_LesHouchesWidth_netZ_Q (ω : Weights n L) (x : Fin (n 0) → ℝ) :
    ∀ m (i : Fin (n (m + 1))), netZ ω x (m + 1) i = W5_LesHouchesWidth_Q ω x m i.val := by
  intro m
  induction m with
  | zero => exact W5_LesHouchesWidth_base ω x
  | succ m ih => exact W5_LesHouchesWidth_step ω x m ih

end Paths

theorem solution {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L)
    (x : Fin (n 0) → ℝ) (q : Fin (n (L + 1))) :
    output ω x q =
      ∑ p : Fin (n 0), x p *
        ∑ γ ∈ pathsFromTo n L p q, pathWeight ω γ * pathActivation ω x γ := by
  classical
  have hsum : ∀ g : NetPath n L → ℝ, ∑ p : Fin (n 0), x p * ∑ γ ∈ pathsFromTo n L p q, g γ =
      ∑ γ : NetPath n L, if γ (Fin.last (L + 1)) = q then x (γ 0) * g γ else 0 := by
    intro g
    simp only [pathsFromTo, Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    refine (Finset.sum_eq_single (γ 0) (fun p _ hp => ?_)
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · split_ifs with h
      · exact absurd h.1.symm hp
      · rw [mul_zero]
    · split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.2 h2
      · exact absurd ⟨rfl, h2⟩ h1
      · simp
  rw [output, W5_LesHouchesWidth_netZ_Q ω x L q, hsum]
  unfold W5_LesHouchesWidth_Q
  refine Finset.sum_congr rfl fun γ _ => ?_
  have hW : pathWeight ω γ = ∏ ℓ : Fin (L + 1),
      W5_LesHouchesWidth_wv ω ℓ.val (γ ℓ.succ).val (γ ℓ.castSucc).val :=
    Finset.prod_congr rfl fun ℓ _ => W5_LesHouchesWidth_weight_eq ω ℓ.val (γ ℓ.succ) (γ ℓ.castSucc)
  have hA : pathActivation ω x γ = ∏ ℓ : Fin L,
      W5_LesHouchesWidth_av ω x (ℓ.val + 1) (γ ⟨ℓ.val + 1, by omega⟩).val :=
    Finset.prod_congr rfl fun ℓ _ =>
      (W5_LesHouchesWidth_av_eq ω x (ℓ.val + 1) (γ ⟨ℓ.val + 1, by omega⟩)).symm
  have hx : x (γ 0) = W5_LesHouchesWidth_xv x (γ 0).val := by
    have hlt : (γ 0).val < n 0 := (γ 0).isLt
    unfold W5_LesHouchesWidth_xv
    rw [dif_pos hlt]
    rfl
  rw [hW, hA, hx]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd (Fin.ext h1) h2
  · exact absurd (congrArg Fin.val h2) h1
  · rfl
