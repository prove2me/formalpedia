-- Prove2me | solution 1 for ManneLP.Equilibrium.lp_optimum_gives_optimal_rule
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T12:58:33.248496+00:00
-- url     : https://prove2.me/submissions/66f4b989-e7de-491b-95f9-855a38935edb

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_Chain
import Definitions.Def_ManneLP_Equilibrium_LP

set_option autoImplicit false

namespace ManneLP.Equilibrium.Aux
open ManneLP.Equilibrium

lemma sum_A (M : Model) (f : ℕ × ℕ → ℝ) :
    ∑ a ∈ M.A, f a = ∑ i ∈ states M, ∑ j ∈ actions M i, f (i, j) := by
  apply Finset.sum_finset_product
  intro a
  constructor
  · intro h
    have := M.A_le a h
    simp only [states, actions, Finset.mem_range, Finset.mem_filter]
    exact ⟨by omega, by omega, by simpa using h⟩
  · rintro ⟨-, h⟩
    simp only [actions, Finset.mem_filter] at h
    simpa using h.2

lemma mem_actions (M : Model) {i j : ℕ} (h : (i, j) ∈ M.A) : j ∈ actions M i := by
  have := M.A_le _ h
  dsimp only at this
  simp only [actions, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, h⟩

lemma termProb_sum (M : Model) (k : ℕ) (hk : k ≤ M.T) :
    ∑ t ∈ states M, termProb M k t = 1 := by
  unfold termProb
  have hs : ∀ t ∈ states M, Summable (fun n : ℕ => if k - n = t then M.p n else 0) := by
    intro t _
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) M.p_hasSum.summable
    · split_ifs
      · exact M.p_nonneg n
      · exact le_refl 0
    · split_ifs
      · exact le_refl _
      · exact M.p_nonneg n
  rw [← Summable.tsum_finsetSum hs]
  have : ∀ n : ℕ, (∑ t ∈ states M, if k - n = t then M.p n else 0) = M.p n := by
    intro n
    rw [Finset.sum_ite_eq, if_pos]
    simp only [states, Finset.mem_range]
    omega
  simp_rw [this]
  exact M.p_hasSum.tsum_eq

lemma rhsPos_eq (M : Model) (x : ℕ × ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    rhsPos M x t = ∑ a ∈ M.A, x a * termProb M (a.1 + a.2) t := by
  unfold rhsPos termProb
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← tsum_mul_left]
  congr 1
  funext n
  by_cases h : a.1 + a.2 - n = t
  · have h' : (a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) = (t : ℤ) := by omega
    rw [if_pos h, if_pos h']
    ring
  · have h' : ¬ ((a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) = (t : ℤ)) := by omega
    rw [if_neg h, if_neg h']
    ring

lemma rhsPos_lin (M : Model) (x : ℕ × ℕ → ℝ) (t : ℕ) :
    rhsPos M x t = ∑ a ∈ M.A, (∑' n : ℕ,
      if (a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) = (t : ℤ) then M.p n else 0) * x a := by
  unfold rhsPos
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← tsum_mul_right]
  congr 1
  funext n
  split_ifs <;> ring

lemma expCost_eq (M : Model) (x : ℕ × ℕ → ℝ) : expCost M x = lpObj M x := by
  have hp : ∑' n, M.p n = 1 := M.p_hasSum.tsum_eq
  unfold expCost expC₁ expC₂ expC₃ lpObj costCoeff
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e1 : ∑' n : ℕ, x a * M.p n * M.C₁ a.1 = x a * M.C₁ a.1 := by
    have : (fun n : ℕ => x a * M.p n * M.C₁ a.1) = fun n => M.p n * (x a * M.C₁ a.1) := by
      funext n; ring
    rw [this, tsum_mul_right, hp, one_mul]
  have e2 : ∑' n : ℕ, x a * M.p n * M.C₂ a.2 = x a * M.C₂ a.2 := by
    have : (fun n : ℕ => x a * M.p n * M.C₂ a.2) = fun n => M.p n * (x a * M.C₂ a.2) := by
      funext n; ring
    rw [this, tsum_mul_right, hp, one_mul]
  have e3 : ∑' n : ℕ, x a * M.p n * M.C₃ ((n : ℤ) - (a.1 : ℤ) - (a.2 : ℤ)) =
      x a * ∑' n : ℕ, M.p n * M.C₃ ((n : ℤ) - (a.1 : ℤ) - (a.2 : ℤ)) := by
    rw [← tsum_mul_left]
    congr 1
    funext n
    ring
  rw [e1, e2, e3]
  ring

lemma marginal_nonneg (M : Model) (x : ℕ × ℕ → ℝ) (hx : ∀ a ∈ M.A, 0 ≤ x a) (i : ℕ) :
    0 ≤ marginal M x i :=
  Finset.sum_nonneg fun _ hj => hx _ (Finset.mem_filter.1 hj).2

lemma joint_decode (M : Model) (x : ℕ × ℕ → ℝ) (hx : ∀ a ∈ M.A, 0 ≤ x a)
    (a : ℕ × ℕ) (ha : a ∈ M.A) :
    jointLaw (decodeDist M x) (decodeRule M x) a = x a := by
  obtain ⟨i, j⟩ := a
  simp only [jointLaw, decodeDist, decodeRule]
  rw [if_pos ha]
  by_cases h : marginal M x i = 0
  · have h' := h
    unfold marginal at h'
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj => hx _ (Finset.mem_filter.1 hj).2)).1 h' j (mem_actions M ha)
    rw [h, zero_mul, hz]
  · rw [if_pos (show marginal M x i ≠ 0 from h)]
    field_simp

lemma sum_trans (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) (t : ℕ) :
    ∑ i ∈ states M, y i * trans M q i t =
      ∑ a ∈ M.A, jointLaw y q a * termProb M (a.1 + a.2) t := by
  rw [sum_A]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold trans jointLaw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma decode_isRule (M : Model) (x : ℕ × ℕ → ℝ) (hx : ∀ a ∈ M.A, 0 ≤ x a) :
    IsRule M (decodeRule M x) := by
  refine ⟨fun i j => ?_, fun i j h => ?_, fun i hi => ?_⟩
  · unfold decodeRule
    split_ifs with h1 h2 h3
    · exact div_nonneg (hx _ h1) (marginal_nonneg M x hx i)
    · norm_num
    · exact le_refl 0
    · exact le_refl 0
  · unfold decodeRule
    rw [if_neg h]
  · by_cases hm : marginal M x i = 0
    · have h0 : 0 ∈ actions M i := mem_actions M (M.zero_mem i hi)
      rw [Finset.sum_eq_single 0]
      · simp [decodeRule, M.zero_mem i hi, hm]
      · intro b _ hb0
        simp [decodeRule, hm, hb0]
      · intro h
        exact absurd h0 h
    · calc ∑ j ∈ actions M i, decodeRule M x i j
            = ∑ j ∈ actions M i, x (i, j) / marginal M x i := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hA : (i, j) ∈ M.A := (Finset.mem_filter.1 hj).2
              simp only [decodeRule]
              rw [if_pos hA, if_pos (show marginal M x i ≠ 0 from hm)]
        _ = 1 := by
              rw [← Finset.sum_div]
              exact div_self hm

lemma decode_isEq (M : Model) (x : ℕ × ℕ → ℝ) (hfeas : IsLPFeasible M x) :
    IsEquilibrium M (decodeRule M x) (decodeDist M x) := by
  obtain ⟨hx, hsum, h8⟩ := hfeas
  have hR : ∀ t, ∑ i ∈ states M, decodeDist M x i * trans M (decodeRule M x) i t
      = ∑ a ∈ M.A, x a * termProb M (a.1 + a.2) t := by
    intro t
    rw [sum_trans]
    exact Finset.sum_congr rfl fun a ha => by rw [joint_decode M x hx a ha]
  have hmarg : ∑ t ∈ states M, marginal M x t = 1 := by
    rw [← hsum, sum_A]
    rfl
  have hRs : ∑ t ∈ states M, ∑ a ∈ M.A, x a * termProb M (a.1 + a.2) t = 1 := by
    rw [Finset.sum_comm, ← hsum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.mul_sum, termProb_sum M _ (M.A_le a ha), mul_one]
  refine ⟨fun i _ => marginal_nonneg M x hx i, hmarg, fun t ht => ?_⟩
  rw [hR]
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0
    have hpos_eq : ∀ s ∈ Finset.range M.T, marginal M x (s + 1) =
        ∑ a ∈ M.A, x a * termProb M (a.1 + a.2) (s + 1) := by
      intro s hs
      have hsT : s < M.T := Finset.mem_range.1 hs
      have := h8 (s + 1) (by omega) (by omega)
      rw [Eq8t, rhsPos_eq M x _ (by omega)] at this
      exact this
    unfold states at hmarg hRs
    rw [Finset.sum_range_succ'] at hmarg hRs
    rw [Finset.sum_congr rfl hpos_eq] at hmarg
    show marginal M x 0 = _
    linarith
  · have := h8 t hpos ht
    rw [Eq8t, rhsPos_eq M x _ hpos] at this
    exact this

lemma joint_feasible (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) (hq : IsRule M q)
    (hy : IsEquilibrium M q y) : IsLPFeasible M (jointLaw y q) := by
  obtain ⟨hq0, -, hq1⟩ := hq
  obtain ⟨hy0, hy1, hyt⟩ := hy
  refine ⟨fun a ha => ?_, ?_, fun t ht1 htT => ?_⟩
  · have := M.A_le a ha
    exact mul_nonneg (hy0 _ (by omega)) (hq0 _ _)
  · rw [sum_A, ← hy1]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiT : i ≤ M.T := by
      simp only [states, Finset.mem_range] at hi
      omega
    simp only [jointLaw]
    rw [← Finset.mul_sum, hq1 i hiT, mul_one]
  · unfold Eq8t
    rw [rhsPos_eq M _ t ht1, ← sum_trans, ← hyt t htT]
    simp only [marginal, jointLaw]
    rw [← Finset.mul_sum, hq1 t htT, mul_one]

lemma lpObj_congr (M : Model) (x x' : ℕ × ℕ → ℝ) (h : ∀ a ∈ M.A, x a = x' a) :
    lpObj M x = lpObj M x' := by
  unfold lpObj
  exact Finset.sum_congr rfl fun a ha => by rw [h a ha]

lemma eqCost_joint (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    eqCost M q y = lpObj M (jointLaw y q) :=
  expCost_eq M _

lemma exists_opt (M : Model) : ∃ x, IsLPOptimal M x := by
  let S : Set (ℕ × ℕ → ℝ) := {x | IsLPFeasible M x ∧ ∀ a, a ∉ M.A → x a = 0}
  have hS_sub : S ⊆ Set.pi Set.univ (fun _ => Set.Icc (0:ℝ) 1) := by
    rintro x ⟨⟨hx0, hx1, -⟩, hout⟩ a -
    by_cases ha : a ∈ M.A
    · refine ⟨hx0 a ha, ?_⟩
      rw [← hx1]
      exact Finset.single_le_sum hx0 ha
    · rw [hout a ha]
      exact ⟨le_refl 0, zero_le_one⟩
  have hcont_lp : Continuous (lpObj M) := by
    unfold lpObj
    exact continuous_finsetSum _ fun a _ => continuous_const.mul (continuous_apply a)
  have hclosed : IsClosed S := by
    have e : S = (⋂ a ∈ (M.A : Set (ℕ × ℕ)), {x : ℕ × ℕ → ℝ | 0 ≤ x a}) ∩
        {x : ℕ × ℕ → ℝ | ∑ a ∈ M.A, x a = 1} ∩
        (⋂ t ∈ {t : ℕ | 1 ≤ t ∧ t ≤ M.T}, {x : ℕ × ℕ → ℝ | marginal M x t =
          ∑ a ∈ M.A, (∑' n : ℕ, if (a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) = (t : ℤ)
            then M.p n else 0) * x a}) ∩
        (⋂ a ∈ (M.A : Set (ℕ × ℕ))ᶜ, {x : ℕ × ℕ → ℝ | x a = 0}) := by
      ext x
      simp only [S, IsLPFeasible, Eq8t, rhsPos_lin, Set.mem_ofPred_eq, Set.mem_inter_iff,
        Set.mem_iInter, Set.mem_compl_iff, Finset.mem_coe, and_imp]
      tauto
    rw [e]
    refine ((IsClosed.inter (IsClosed.inter ?_ ?_) ?_).inter ?_)
    · exact isClosed_biInter fun a _ => isClosed_le continuous_const (continuous_apply a)
    · exact isClosed_eq (continuous_finsetSum _ fun a _ => continuous_apply a) continuous_const
    · refine isClosed_biInter fun t _ => isClosed_eq ?_ ?_
      · unfold marginal
        exact continuous_finsetSum _ fun j _ => continuous_apply _
      · exact continuous_finsetSum _ fun a _ => continuous_const.mul (continuous_apply a)
    · exact isClosed_biInter fun a _ => isClosed_eq (continuous_apply a) continuous_const
  have hcpt : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hS_sub
  have h00 : ((0 : ℕ), (0 : ℕ)) ∈ M.A := M.zero_mem 0 (Nat.zero_le _)
  obtain ⟨x0, hx0⟩ : ∃ x0 : ℕ × ℕ → ℝ, ∀ a, x0 a = if a = (0, 0) then 1 else 0 :=
    ⟨_, fun _ => rfl⟩
  have hne : S.Nonempty := by
    refine ⟨x0, ⟨?_, ?_, fun t ht1 _ => ?_⟩, fun a ha => ?_⟩
    · intro a _
      rw [hx0]
      split_ifs <;> norm_num
    · simp only [hx0]
      rw [Finset.sum_ite_eq']
      simp [h00]
    · unfold Eq8t marginal rhsPos
      have hL : ∑ j ∈ actions M t, x0 (t, j) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hx0, if_neg]
        intro h
        simp only [Prod.mk.injEq] at h
        omega
      have hRz : ∑ a ∈ M.A, ∑' n : ℕ, (if (a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) = (t : ℤ)
          then M.p n * x0 a else 0) = 0 := by
        refine Finset.sum_eq_zero fun a _ => ?_
        have : ∀ n : ℕ, (if (a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) = (t : ℤ)
            then M.p n * x0 a else 0) = 0 := by
          intro n
          by_cases ha : a = (0, 0)
          · subst ha
            rw [if_neg]
            intro h
            dsimp only at h
            omega
          · simp [hx0, ha]
        simp only [this, tsum_zero]
      rw [hL, hRz]
    · rw [hx0, if_neg]
      rintro rfl
      exact ha h00
  obtain ⟨x, hxS, hmin⟩ := hcpt.exists_isMinOn hne hcont_lp.continuousOn
  refine ⟨x, hxS.1, fun x' hx' => ?_⟩
  obtain ⟨x'', hagree, hout⟩ : ∃ x'' : ℕ × ℕ → ℝ, (∀ a ∈ M.A, x'' a = x' a) ∧
      ∀ a, a ∉ M.A → x'' a = 0 :=
    ⟨fun a => if a ∈ M.A then x' a else 0, fun a ha => if_pos ha, fun a ha => if_neg ha⟩
  have hm : ∀ t, marginal M x'' t = marginal M x' t := fun t =>
    Finset.sum_congr rfl fun j hj => hagree (t, j) (Finset.mem_filter.1 hj).2
  have hr : ∀ t, rhsPos M x'' t = rhsPos M x' t := by
    intro t
    unfold rhsPos
    exact Finset.sum_congr rfl fun a ha => by rw [hagree a ha]
  have hx''S : x'' ∈ S := by
    obtain ⟨h0, h1, h8⟩ := hx'
    refine ⟨⟨fun a ha => ?_, ?_, fun t ht1 htT => ?_⟩, hout⟩
    · rw [hagree a ha]
      exact h0 a ha
    · rw [Finset.sum_congr rfl hagree]
      exact h1
    · have := h8 t ht1 htT
      unfold Eq8t at this ⊢
      rw [hm, hr]
      exact this
  rw [lpObj_congr M x' x'' (fun a ha => (hagree a ha).symm)]
  exact hmin hx''S

end ManneLP.Equilibrium.Aux

open ManneLP.Equilibrium in
theorem solution (M : Model)
    (hsum : ∀ a ∈ M.A,
      Summable (fun n : ℕ => M.p n * M.C₃ ((n : ℤ) - (a.1 : ℤ) - (a.2 : ℤ)))) :
    (∃ x : ℕ × ℕ → ℝ, IsLPOptimal M x) ∧
    ∀ x : ℕ × ℕ → ℝ, IsLPOptimal M x →
      IsRule M (decodeRule M x) ∧
      IsEquilibrium M (decodeRule M x) (decodeDist M x) ∧
      eqCost M (decodeRule M x) (decodeDist M x) = lpObj M x ∧
      ∀ (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ), IsRule M q → IsEquilibrium M q y →
        eqCost M (decodeRule M x) (decodeDist M x) ≤ eqCost M q y := by
  refine ⟨Aux.exists_opt M, fun x hx => ?_⟩
  obtain ⟨hfeas, hmin⟩ := hx
  have hx0 := hfeas.1
  refine ⟨Aux.decode_isRule M x hx0, Aux.decode_isEq M x hfeas, ?_, fun q y hq hy => ?_⟩
  · rw [Aux.eqCost_joint]
    exact Aux.lpObj_congr M _ _ (Aux.joint_decode M x hx0)
  · rw [Aux.eqCost_joint, Aux.eqCost_joint, Aux.lpObj_congr M _ x (Aux.joint_decode M x hx0)]
    exact hmin _ (Aux.joint_feasible M q y hq hy)
