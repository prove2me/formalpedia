-- Prove2me | solution 1 for LocalOccupancyIS.Glauber.corollary_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:25:36.449993+00:00
-- url     : https://prove2.me/submissions/8ae7869c-189d-4172-aed1-42cbbab0b3e5

import Theorems.Thm_LocalOccupancyIS_Glauber_bit_regime_uniform
import Theorems.Thm_LocalOccupancyIS_Glauber_three_sweep_finite
import Definitions.Def_LocalOccupancyIS_Glauber_Dynamics
import Theorems.Thm_SinkhornHall_lemma_1_1
import Definitions.Def_LocalOccupancyIS_Glauber_Parameters
import Definitions.Def_LocalOccupancyIS_Glauber_Execution
import Theorems.Thm_LocalOccupancyIS_Glauber_lemma_7
import Definitions.Def_LocalOccupancyIS_Glauber_GoalInterface

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma empty_hardcore (G : SimpleGraph V) : MarkovMixing.IsHardcore G (fun _ => false) := by
  intro v w h
  simp

instance stateNonempty (G : SimpleGraph V) : Nonempty (State G) :=
  ⟨⟨_, empty_hardcore G⟩⟩

lemma hcWeight_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : V → Bool) : 0 ≤ MarkovMixing.hardcoreWeight G lam σ := by
  unfold MarkovMixing.hardcoreWeight
  split_ifs
  · exact le_of_lt (pow_pos hlam _)
  · rfl

lemma hcPartition_pos (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) : 0 < ∑ σ : V → Bool, MarkovMixing.hardcoreWeight G lam σ := by
  apply Finset.sum_pos'
  · intro σ hσ
    exact hcWeight_nonneg G hlam σ
  · refine ⟨fun _ => false, Finset.mem_univ _, ?_⟩
    simp [MarkovMixing.hardcoreWeight, empty_hardcore]

lemma hcLaw_pos (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) : 0 < HardCoreBochner.hcLaw G lam σ := by
  apply div_pos _ (hcPartition_pos G hlam)
  simp only [MarkovMixing.hardcoreWeight, if_pos σ.property]
  exact pow_pos hlam _

lemma hcLaw_dist (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) : MarkovMixing.IsDist (HardCoreBochner.hcLaw G lam) := by
  constructor
  · intro σ; exact (hcLaw_pos G hlam σ).le
  · unfold HardCoreBochner.hcLaw MarkovMixing.hardcoreDist
    rw [← Finset.sum_div]
    have heq : (∑ σ : State G, MarkovMixing.hardcoreWeight G lam σ.val) =
        ∑ σ : V → Bool, MarkovMixing.hardcoreWeight G lam σ := by
      calc
        _ = ∑ σ ∈ Finset.univ.filter (MarkovMixing.IsHardcore G),
            MarkovMixing.hardcoreWeight G lam σ :=
          (Finset.sum_subtype _ (by simp) _).symm
        _ = _ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro σ _
          by_cases hs : MarkovMixing.IsHardcore G σ <;>
            simp [hs, MarkovMixing.hardcoreWeight]
    rw [heq, div_self (ne_of_gt (hcPartition_pos G hlam))]

lemma heatBath_stochastic (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (A : Finset V) : MarkovMixing.IsStochastic (heatBath G lam A) := by
  classical
  have hp := hcLaw_pos G hlam
  have hden (σ : State G) : 0 < ∑ ζ : State G,
      if ∀ v ∉ A, ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0 := by
    apply Finset.sum_pos'
    · intro ζ _
      split_ifs
      · exact (hp ζ).le
      · rfl
    · exact ⟨σ, Finset.mem_univ _, by simpa using hp σ⟩
  constructor
  · intro σ τ
    unfold heatBath
    split_ifs
    · exact (div_pos (hp τ) (hden σ)).le
    · rfl
  · intro σ
    unfold heatBath
    simp_rw [show ∀ (c : Prop) [Decidable c] (a b : ℝ), (if c then a / b else 0) = (if c then a else 0) / b from fun c _ a b => by split_ifs <;> simp]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (hden σ))

lemma push_dist {Ω : Type} [Fintype Ω] {ν : Ω → ℝ} {K : Matrix Ω Ω ℝ}
    (hν : MarkovMixing.IsDist ν) (hK : MarkovMixing.IsStochastic K) :
    MarkovMixing.IsDist (push ν K) := by
  constructor
  · intro y
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hν.1 x) (hK.1 x y))
  · change (∑ y, ∑ x, ν x * K x y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hK.2, mul_one]
    exact hν.2

lemma finite_pinsker {Ω : Type} [Fintype Ω] [Nonempty Ω] {ν μ : Ω → ℝ}
    (hν : MarkovMixing.IsDist ν) (hμ : MarkovMixing.IsDist μ) (hd : Dominated ν μ) :
    2 * tv ν μ ^ 2 ≤ kl ν μ := by
  classical
  have h := SinkhornHall.lemma_1_1 ν μ hν.1 hμ.1 (hν.2.trans hμ.2.symm)
  have hn : ¬ ∃ x, μ x = 0 ∧ 0 < ν x := by
    rintro ⟨x, hx, hv⟩
    have := hd x hv.ne'
    linarith
  rw [SinkhornHall.klDiv, if_neg hn, hν.2] at h
  have he : kl ν μ = ∑ x, ν x * Real.log (ν x / μ x) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ν x = 0 <;> simp [hx]
  rw [he]
  have hr : (∑ x, |ν x - μ x|) ^ 2 / 2 ≤ ∑ x, ν x * Real.log (ν x / μ x) := by
    exact_mod_cast h
  unfold tv
  nlinarith

lemma heatBath_dominated (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (A : Finset V) {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) : Dominated ν (push ν (heatBath G lam A)) := by
  classical
  intro σ hσ
  have hd : 0 < ∑ ζ : State G,
      if ∀ v ∉ A, ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0 := by
    apply Finset.sum_pos'
    · intro ζ _
      split_ifs
      · exact (hcLaw_pos G hlam ζ).le
      · rfl
    · exact ⟨σ, Finset.mem_univ _, by simpa using hcLaw_pos G hlam σ⟩
  have hdiag : 0 < heatBath G lam A σ σ := by
    simpa [heatBath] using div_pos (hcLaw_pos G hlam σ) hd
  have hσpos : 0 < ν σ := lt_of_le_of_ne (hν.1 σ) (Ne.symm hσ)
  have hstoch := heatBath_stochastic G hlam A
  exact (mul_pos hσpos hdiag).trans_le
    (Finset.single_le_sum (fun x _ => mul_nonneg (hν.1 x) (hstoch.1 x σ)) (Finset.mem_univ σ))

lemma kl_eq_sum {Ω : Type} [Fintype Ω] (ν μ : Ω → ℝ) :
    kl ν μ = ∑ x, ν x * Real.log (ν x / μ x) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ν x = 0 <;> simp [hx]


end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {Ω : Type} [Fintype Ω]

lemma tv_nonneg (ν μ : Ω → ℝ) : 0 ≤ tv ν μ := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

lemma tv_symm (ν μ : Ω → ℝ) : tv ν μ = tv μ ν := by
  unfold tv
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

lemma tv_triangle (ν μ ρ : Ω → ℝ) : tv ν ρ ≤ tv ν μ + tv μ ρ := by
  unfold tv
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (x : Ω) _ => abs_sub_le (ν x) (μ x) (ρ x))
  rw [Finset.sum_add_distrib] at h
  linarith

lemma tv_contraction (ν μ : Ω → ℝ) {K : Matrix Ω Ω ℝ}
    (hK : MarkovMixing.IsStochastic K) : tv (push ν K) (push μ K) ≤ tv ν μ := by
  unfold tv
  suffices (∑ y, |push ν K y - push μ K y|) ≤ ∑ x, |ν x - μ x| by linarith
  calc
    _ ≤ ∑ y, ∑ x, |ν x - μ x| * K x y := by
      apply Finset.sum_le_sum
      intro y _
      change |(∑ x, ν x * K x y) - ∑ x, μ x * K x y| ≤ _
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ x, |ν x * K x y - μ x * K x y| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← sub_mul, abs_mul, abs_of_nonneg (hK.1 x y)]
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hK.2, mul_one]

lemma expectation_tv {ν μ : Ω → ℝ} (hν : MarkovMixing.IsDist ν)
    (hμ : MarkovMixing.IsDist μ) (f : Ω → ℝ) {L : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ L) :
    |expectation ν f - expectation μ f| ≤ L * tv ν μ := by
  have heq : expectation ν f - expectation μ f = ∑ x, (ν x - μ x) * (f x - L/2) := by
    unfold expectation
    simp_rw [sub_mul, mul_sub]
    simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hν.2, hμ.2]
    ring
  rw [heq]
  calc
    _ ≤ ∑ x, |(ν x - μ x) * (f x - L/2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |ν x - μ x| * (L/2) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply abs_le.mpr
      constructor <;> linarith [(hf x).1, (hf x).2]
    _ = _ := by rw [← Finset.sum_mul]; unfold tv; ring

lemma push_push (ν : Ω → ℝ) (K L : Matrix Ω Ω ℝ) : push (push ν K) L = push ν (K*L) := by
  exact Matrix.vecMul_vecMul ν K L

lemma word_append {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (w w' : List V) :
    word G lam (w ++ w') = word G lam w * word G lam w' := by
  simp [word]

lemma word_stochastic {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam) (w : List V) :
    MarkovMixing.IsStochastic (word G lam w) := by
  classical
  induction w with
  | nil =>
    constructor
    · intro σ τ
      simp only [word, List.map_nil, List.prod_nil, Matrix.one_apply]
      split_ifs <;> norm_num
    · intro σ
      simp [word, Matrix.one_apply]
  | cons u w ih =>
    have hP := heatBath_stochastic G hlam {u}
    change MarkovMixing.IsStochastic (P G lam u * word G lam w)
    constructor
    · intro σ τ
      exact Finset.sum_nonneg fun ζ _ => mul_nonneg (hP.1 σ ζ) (ih.1 ζ τ)
    · intro σ
      change (∑ τ, ∑ ζ, P G lam u σ ζ * word G lam w ζ τ) = 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ih.2, mul_one]
      exact hP.2 σ

lemma tv_word_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam)
    (ν : State G → ℝ) (w : List V) :
    tv ν (push ν (word G lam w)) ≤ (w.map (fun u => tv ν (push ν (P G lam u)))).sum := by
  classical
  induction w with
  | nil => simp [word, push, tv, Matrix.vecMul_one]
  | cons u w ih =>
    change tv ν (push ν (P G lam u * word G lam w)) ≤ _
    rw [← push_push]
    calc
      _ ≤ tv ν (push ν (word G lam w)) +
          tv (push ν (word G lam w)) (push (push ν (P G lam u)) (word G lam w)) := tv_triangle _ _ _
      _ ≤ (w.map (fun u => tv ν (push ν (P G lam u)))).sum + tv ν (push ν (P G lam u)) :=
        add_le_add ih (tv_contraction _ _ (word_stochastic G hlam w))
      _ = _ := by simp; ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma full_fiber_sum (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (σ : State G) (u : V) :
    (∑ ζ : State G, if ∀ v, v ≠ u → ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0) =
    ∑ ζ ∈ Finset.univ.filter (fun ζ : V → Bool => ∀ v, v ≠ u → ζ v = σ.val v),
      MarkovMixing.hardcoreDist G lam ζ := by
  classical
  calc
    _ = ∑ ζ ∈ Finset.univ.filter (MarkovMixing.IsHardcore G),
        if ∀ v, v ≠ u → ζ v = σ.val v then MarkovMixing.hardcoreDist G lam ζ else 0 := by
      exact (Finset.sum_subtype (p := MarkovMixing.IsHardcore G)
        (Finset.univ.filter (MarkovMixing.IsHardcore G)) (by intro ζ; simp)
        (fun ζ => if ∀ v, v ≠ u → ζ v = σ.val v then MarkovMixing.hardcoreDist G lam ζ else 0)).symm
    _ = _ := by
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ζ _
      by_cases hz : MarkovMixing.IsHardcore G ζ
      · simp [hz]
      · simp [hz, MarkovMixing.hardcoreDist, MarkovMixing.hardcoreWeight]

lemma scan_eq (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) :
    K G lam = (Fintype.card V : ℝ)⁻¹ • ∑ u, P G lam u := by
  classical
  ext σ τ
  simp only [K, HardCoreBochner.hcChain, MarkovMixing.subChain, MarkovMixing.glauber,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  simp only [P, heatBath, Finset.mem_singleton]
  rw [full_fiber_sum]
  rfl

lemma scan_stochastic [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) : MarkovMixing.IsStochastic (K G lam) := by
  classical
  rw [scan_eq]
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  constructor
  · intro σ τ
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    change 0 ≤ (Fintype.card V : ℝ)⁻¹ * ∑ u, P G lam u σ τ
    exact mul_nonneg (inv_nonneg.mpr hn.le)
      (Finset.sum_nonneg (fun u _ => (heatBath_stochastic G hlam {u}).1 σ τ))
  · intro σ
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    change (∑ τ, (Fintype.card V : ℝ)⁻¹ * ∑ u, P G lam u σ τ) = 1
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hrow (u : V) : ∑ τ, P G lam u σ τ = 1 := (heatBath_stochastic G hlam {u}).2 σ
    simp_rw [hrow]
    simp [hn.ne']

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma update_false_hardcore (G : SimpleGraph V) {σ : V → Bool}
    (hσ : MarkovMixing.IsHardcore G σ) (u : V) :
    MarkovMixing.IsHardcore G (Function.update σ u false) := by
  intro v w hvw
  by_cases hv : v = u
  · subst v; simp
  by_cases hw : w = u
  · subst w; simp
  simpa [Function.update_of_ne hv, Function.update_of_ne hw] using hσ v w hvw

lemma update_true_hardcore (G : SimpleGraph V) [DecidableRel G.Adj] {σ : V → Bool}
    (hσ : MarkovMixing.IsHardcore G σ) (u : V)
    (hu : ∀ v ∈ G.neighborFinset u, σ v = false) :
    MarkovMixing.IsHardcore G (Function.update σ u true) := by
  intro v w hvw
  by_cases hv : v = u
  · subst v
    have hw : w ≠ u := G.ne_of_adj hvw.symm
    simp [Function.update_of_ne hw, hu w (by simpa using hvw)]
  by_cases hw : w = u
  · subst w
    simp [Function.update_of_ne hv, hu v (by simpa using hvw.symm)]
  simpa [Function.update_of_ne hv, Function.update_of_ne hw] using hσ v w hvw

lemma spin_hardcore (G : SimpleGraph V) [DecidableRel G.Adj] (σ : State G)
    (u : V) (coin : Bool) : MarkovMixing.IsHardcore G (updateSpin G σ.val u coin) := by
  unfold updateSpin
  split_ifs with h
  · cases coin
    · exact update_false_hardcore G σ.property u
    · exact update_true_hardcore G σ.property u h
  · exact update_false_hardcore G σ.property u

lemma size_update_true (σ : V → Bool) (u : V) :
    size (Function.update σ u true) = size (Function.update σ u false) + 1 := by
  classical
  have hset : (Finset.univ.filter (fun v => Function.update σ u true v = true)) =
      insert u (Finset.univ.filter (fun v => Function.update σ u false v = true)) := by
    ext v
    by_cases hv : v = u <;> simp [hv, Function.update_of_ne]
  have hu : u ∉ Finset.univ.filter (fun v => Function.update σ u false v = true) := by simp
  unfold size
  rw [hset, Finset.card_insert_of_notMem hu]

lemma exterior_two (σ τ : V → Bool) (u : V)
    (he : ∀ v, v ≠ u → τ v = σ v) :
    τ = Function.update σ u false ∨ τ = Function.update σ u true := by
  have hu : τ = Function.update σ u (τ u) := by
    ext v
    by_cases hv : v = u
    · simp [hv]
    · simp [Function.update_of_ne hv, he v hv]
  cases h : τ u
  · exact Or.inl (hu.trans (by rw [h]))
  · exact Or.inr (hu.trans (by rw [h]))

lemma full_fiber_two (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (σ : State G) (u : V) :
    (∑ ζ ∈ Finset.univ.filter (fun ζ : V → Bool => ∀ v, v ≠ u → ζ v = σ.val v),
      MarkovMixing.hardcoreDist G lam ζ) =
      MarkovMixing.hardcoreDist G lam (Function.update σ.val u false) +
      MarkovMixing.hardcoreDist G lam (Function.update σ.val u true) := by
  classical
  have he : Finset.univ.filter (fun ζ : V → Bool => ∀ v, v ≠ u → ζ v = σ.val v) =
      {Function.update σ.val u false, Function.update σ.val u true} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact exterior_two σ.val τ u
    · rintro (rfl | rfl) v hv <;> exact Function.update_of_ne hv _ _
  have hne : Function.update σ.val u false ≠ Function.update σ.val u true := by
    intro h
    have := congrFun h u
    simp at this
  rw [he, Finset.sum_pair hne]

lemma raw_true_iff (G : SimpleGraph V) [DecidableRel G.Adj] (σ : State G) (u : V) :
    MarkovMixing.IsHardcore G (Function.update σ.val u true) ↔
      ∀ v ∈ G.neighborFinset u, σ.val v = false := by
  constructor
  · intro h v hv
    have huv : G.Adj u v := by simpa using hv
    have hne : v ≠ u := G.ne_of_adj huv.symm
    have hh := h u v huv
    simp only [Function.update_self, Function.update_of_ne hne] at hh
    cases he : σ.val v <;> simp_all
  · exact update_true_hardcore G σ.property u

lemma raw_true_law (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (σ : State G) (u : V) :
    MarkovMixing.hardcoreDist G lam (Function.update σ.val u true) =
      if ∀ v ∈ G.neighborFinset u, σ.val v = false then
        lam * MarkovMixing.hardcoreDist G lam (Function.update σ.val u false) else 0 := by
  classical
  have h0 := update_false_hardcore G σ.property u
  by_cases h : ∀ v ∈ G.neighborFinset u, σ.val v = false
  · rw [if_pos h]
    have h1 := (raw_true_iff G σ u).mpr h
    simp only [MarkovMixing.hardcoreDist, MarkovMixing.hardcoreWeight, if_pos h0, if_pos h1]
    change lam ^ size (Function.update σ.val u true) / _ = lam * (lam ^ size (Function.update σ.val u false) / _)
    rw [size_update_true, pow_succ]
    ring
  · rw [if_neg h]
    have h1 : ¬ MarkovMixing.IsHardcore G (Function.update σ.val u true) :=
      mt (raw_true_iff G σ u).mp h
    simp [MarkovMixing.hardcoreDist, MarkovMixing.hardcoreWeight, h1]

lemma single_site_formula (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ τ : State G) (u : V) :
    P G lam u σ τ =
      (if τ.val = updateSpin G σ.val u true then p lam else 0) +
      (if τ.val = updateSpin G σ.val u false then 1-p lam else 0) := by
  classical
  have h0 := update_false_hardcore G σ.property u
  have hpos : 0 < MarkovMixing.hardcoreDist G lam (Function.update σ.val u false) :=
    hcLaw_pos G hlam ⟨_,h0⟩
  have hne : Function.update σ.val u false ≠ Function.update σ.val u true := by
    intro he
    have := congrFun he u
    simp at this
  have h0ext : ∀ v, v ≠ u → Function.update σ.val u false v = σ.val v := by
    intro v hv; exact Function.update_of_ne hv _ _
  have h1ext : ∀ v, v ≠ u → Function.update σ.val u true v = σ.val v := by
    intro v hv; exact Function.update_of_ne hv _ _
  unfold P heatBath
  simp only [Finset.mem_singleton]
  rw [full_fiber_sum, full_fiber_two, raw_true_law]
  simp only [updateSpin, HardCoreBochner.hcLaw]
  by_cases hu : ∀ v ∈ G.neighborFinset u, σ.val v = false
  · simp only [if_pos hu]
    by_cases he0 : τ.val = Function.update σ.val u false
    · have he1 : τ.val ≠ Function.update σ.val u true := he0 ▸ hne
      simp only [he0, if_pos h0ext, if_neg hne, ite_true, p, zero_add]
      field_simp [hpos.ne', show (1+lam) ≠ 0 by positivity]
      <;> ring
    · by_cases he1 : τ.val = Function.update σ.val u true
      · simp only [he1, if_pos h1ext, if_neg (Ne.symm hne), ite_true, p, add_zero]
        rw [raw_true_law, if_pos hu]
        field_simp [hpos.ne', show (1+lam) ≠ 0 by positivity]
        <;> ring
      · have he : ¬ ∀ v, v ≠ u → τ.val v = σ.val v :=
          fun h => (exterior_two σ.val τ.val u h).elim he0 he1
        simp only [if_neg he, if_neg he0, if_neg he1, add_zero]
  · simp only [if_neg hu]
    by_cases he0 : τ.val = Function.update σ.val u false
    · simp only [he0, if_pos h0ext, ite_true, add_zero]
      rw [div_self hpos.ne']
      ring
    · have he1 : τ.val ≠ Function.update σ.val u true := by
        intro he
        have h := (raw_true_iff G σ u).mp (he ▸ τ.property)
        exact hu h
      have he : ¬ ∀ v, v ≠ u → τ.val v = σ.val v :=
        fun h => (exterior_two σ.val τ.val u h).elim he0 he1
      simp only [if_neg he, if_neg he0, add_zero]

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma size_sum (σ : V → Bool) : (size σ : ℝ) = ∑ v, if σ v = true then 1 else 0 := by
  rw [← Finset.sum_filter]
  simp [size]

lemma nbrSize_sum (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (σ : V → Bool) :
    (nbrSize G u σ : ℝ) = ∑ v, if G.Adj u v then (if σ v = true then 1 else 0) else 0 := by
  classical
  conv_rhs => rw [← Finset.sum_filter]
  have he : Finset.univ.filter (G.Adj u) = G.neighborFinset u := by ext v; simp
  rw [he, ← Finset.sum_filter]
  simp [nbrSize]

lemma nbrSize_zero (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (σ : V → Bool) :
    nbrSize G u σ = 0 ↔ ∀ v ∈ G.neighborFinset u, σ v = false := by
  simp only [nbrSize, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h v hv
    cases hs : σ v <;> simp_all
  · intro h v hv
    simp [h v hv]

lemma degree_sum_bound (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : DegreeBound G Δ) (σ : V → Bool) :
    (∑ u, (nbrSize G u σ : ℝ)) ≤ Δ * size σ := by
  classical
  simp_rw [nbrSize_sum]
  rw [Finset.sum_comm, size_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : σ v = true
  · simp only [hv, ite_true, mul_one]
    have heq : (∑ u : V, if G.Adj u v then (1 : ℝ) else 0) = G.degree v := by
      simp_rw [G.adj_comm (v := v)]
      rw [← Finset.sum_filter]
      simp [← SimpleGraph.mem_neighborFinset]
    rw [heq]
    exact_mod_cast hΔ v
  · simp [hv]

lemma site_occupancy (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) (u : V) :
    (∑ τ : State G, P G lam u σ τ * (if τ.val u = true then (1 : ℝ) else 0)) =
      p lam * (if nbrSize G u σ.val = 0 then 1 else 0) := by
  classical
  let s0 : State G := ⟨updateSpin G σ.val u false, spin_hardcore G σ u false⟩
  let s1 : State G := ⟨updateSpin G σ.val u true, spin_hardcore G σ u true⟩
  have he0 (τ : State G) : (τ.val = updateSpin G σ.val u false) ↔ τ = s0 := by
    constructor
    · intro ht; apply Subtype.ext; exact ht
    · exact congrArg Subtype.val
  have he1 (τ : State G) : (τ.val = updateSpin G σ.val u true) ↔ τ = s1 := by
    constructor
    · intro ht; apply Subtype.ext; exact ht
    · exact congrArg Subtype.val
  simp_rw [single_site_formula G hlam, he0, he1, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [s0, s1, updateSpin, Function.update_self]
  by_cases h : ∀ v ∈ G.neighborFinset u, σ.val v = false
  · simp only [if_pos h, (nbrSize_zero G u σ.val).mpr h, ite_true, Bool.false_eq_true, ite_false, mul_one, mul_zero, add_zero]
  · have hz : nbrSize G u σ.val ≠ 0 := mt (nbrSize_zero G u σ.val).mp h
    simp only [if_neg h, if_neg hz, Bool.false_eq_true, ite_false, mul_zero, add_zero]

lemma expected_site_occupancy (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (u : V) :
    expectation (push ν (P G lam u)) (fun σ => if σ.val u = true then 1 else 0) =
      p lam * expectation ν (fun σ => if nbrSize G u σ.val = 0 then 1 else 0) := by
  unfold expectation
  change (∑ τ, (∑ σ, ν σ * P G lam u σ τ) * _) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, site_occupancy G hlam]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The two feasible outputs of a heat-bath proposal. -/
def spinState (G : SimpleGraph V) [DecidableRel G.Adj] (σ : State G) (u : V) (coin : Bool) : State G :=
  ⟨updateSpin G σ.val u coin, spin_hardcore G σ u coin⟩

lemma single_site_average (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) (u : V) (f : State G → ℝ) :
    (∑ τ : State G, P G lam u σ τ * f τ) =
      p lam * f (spinState G σ u true) + (1-p lam) * f (spinState G σ u false) := by
  classical
  have he (coin : Bool) (τ : State G) : (τ.val = updateSpin G σ.val u coin) ↔ τ = spinState G σ u coin := by
    constructor
    · intro ht; apply Subtype.ext; exact ht
    · exact congrArg Subtype.val
  simp_rw [single_site_formula G hlam, he, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma expectation_push {Ω : Type} [Fintype Ω] (ν : Ω → ℝ) (K : Matrix Ω Ω ℝ) (f : Ω → ℝ) :
    expectation (push ν K) f = ∑ σ, ν σ * ∑ τ, K σ τ * f τ := by
  unfold expectation
  change (∑ τ, (∑ σ, ν σ * K σ τ) * f τ) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]

lemma p_pos {lam : ℝ} (hlam : 0 < lam) : 0 < p lam := by
  exact div_pos hlam (by positivity)

lemma one_sub_p_pos {lam : ℝ} (hlam : 0 < lam) : 0 < 1-p lam := by
  unfold p
  have h : 0 < 1+lam := by positivity
  apply sub_pos.mpr
  exact (div_lt_one h).mpr (by linarith)

/-- Indicator that every vertex in A is unoccupied. -/
def emptyOn (G : SimpleGraph V) (A : Finset V) (σ : State G) : ℝ :=
  if ∀ v ∈ A, σ.val v = false then 1 else 0

lemma emptyOn_nonneg (G : SimpleGraph V) (A : Finset V) (σ : State G) : 0 ≤ emptyOn G A σ := by
  unfold emptyOn; split_ifs <;> norm_num

lemma emptyOn_false_update (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : State G) (u : V) (A : Finset V) :
    emptyOn G A (spinState G σ u false) = emptyOn G (A.erase u) σ := by
  have he : (∀ v ∈ A, (spinState G σ u false).val v = false) ↔ ∀ v ∈ A.erase u, σ.val v = false := by
    constructor
    · intro h v hv
      obtain ⟨hvu,hvA⟩ := Finset.mem_erase.mp hv
      simpa [spinState, updateSpin, Function.update_of_ne hvu] using h v hvA
    · intro h v hv
      by_cases hvu : v = u
      · subst v; simp [spinState, updateSpin]
      · simpa [spinState, updateSpin, Function.update_of_ne hvu] using h v (Finset.mem_erase.mpr ⟨hvu,hv⟩)
  simp only [emptyOn, he]

lemma emptyOn_outside_update (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : State G) (u : V) (A : Finset V) (hu : u ∉ A) (coin : Bool) :
    emptyOn G A (spinState G σ u coin) = emptyOn G A σ := by
  have he : (∀ v ∈ A, (spinState G σ u coin).val v = false) ↔ ∀ v ∈ A, σ.val v = false := by
    have hvu (v : V) (hv : v ∈ A) : v ≠ u := by intro h; exact hu (h ▸ hv)
    simp only [spinState, updateSpin]
    constructor <;> intro h v hv <;> simpa [Function.update_of_ne (hvu v hv)] using h v hv
  simp only [emptyOn, he]

lemma emptyOn_step_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) (u : V) (A : Finset V) :
    (1-p lam) * expectation ν (emptyOn G (A.erase u)) ≤
      expectation (push ν (P G lam u)) (emptyOn G A) := by
  rw [expectation_push]
  simp_rw [single_site_average G hlam, emptyOn_false_update]
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hh : 0 ≤ p lam * emptyOn G A (spinState G σ u true) :=
    mul_nonneg (p_pos hlam).le (emptyOn_nonneg G A _)
  nlinarith [hν.1 σ]

lemma emptyOn_step_outside (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (u : V) (A : Finset V) (hu : u ∉ A) :
    expectation (push ν (P G lam u)) (emptyOn G A) = expectation ν (emptyOn G A) := by
  rw [expectation_push]
  simp_rw [single_site_average G hlam, emptyOn_outside_update G _ u A hu]
  apply Finset.sum_congr rfl
  intro σ _
  ring

lemma emptyOn_word_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν)
    (w : List V) (A : Finset V) (hcover : A ⊆ w.toFinset) :
    (1-p lam)^A.card ≤ expectation (push ν (word G lam w)) (emptyOn G A) := by
  classical
  induction w using List.reverseRecOn generalizing A with
  | nil =>
    have hA : A = ∅ := by simpa using hcover
    subst A
    simp [word, push, emptyOn, expectation, hν.2]
  | append_singleton w u ih =>
    rw [word_append]
    simp only [word, List.map_singleton, List.prod_singleton]
    rw [← push_push]
    by_cases hu : u ∈ A
    · have hc : A.erase u ⊆ w.toFinset := by
        intro v hv
        have hvA := (Finset.mem_erase.mp hv).2
        have hmem := hcover hvA
        simpa [List.toFinset_append, Finset.mem_union, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_singleton, (Finset.mem_erase.mp hv).1] using hmem
      have hh := mul_le_mul_of_nonneg_left (ih (A.erase u) hc) (one_sub_p_pos hlam).le
      have hcA : A.card = (A.erase u).card+1 := by simpa using (Finset.card_erase_add_one hu).symm
      rw [hcA, pow_succ]
      refine le_trans ?_ (emptyOn_step_lower G hlam _ (push_dist hν (word_stochastic G hlam w)) u A)
      simpa [mul_comm] using hh
    · have hc : A ⊆ w.toFinset := by
        intro v hv
        have hmem := hcover hv
        have hvu : v ≠ u := by intro h; exact hu (h ▸ hv)
        simpa [List.toFinset_append, Finset.mem_union, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_singleton, hvu] using hmem
      rw [emptyOn_step_outside G hlam _ u A hu]
      exact ih A hc

lemma point_dist {Ω : Type} [Fintype Ω] [DecidableEq Ω] (x : Ω) : MarkovMixing.IsDist (point x) := by
  constructor
  · intro y; unfold point; split_ifs <;> norm_num
  · simp [point]

lemma site_step_outside (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) {u v : V} (hvu : v ≠ u) :
    expectation (push ν (P G lam u)) (fun σ => if σ.val v = true then (1 : ℝ) else 0) =
      expectation ν (fun σ => if σ.val v = true then 1 else 0) := by
  rw [expectation_push]
  simp_rw [single_site_average G hlam]
  simp only [spinState, updateSpin, Function.update_of_ne hvu]
  apply Finset.sum_congr rfl
  intro σ _
  ring

lemma site_word_outside (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (w : List V) {v : V} (hv : v ∉ w) :
    expectation (push ν (word G lam w)) (fun σ => if σ.val v = true then (1 : ℝ) else 0) =
      expectation ν (fun σ => if σ.val v = true then 1 else 0) := by
  induction w generalizing ν with
  | nil => simp [word, push]
  | cons u w ih =>
    have hparts : v ≠ u ∧ v ∉ w := by simpa using hv
    have hvu := hparts.1
    have hvw := hparts.2
    change expectation (push ν (P G lam u * word G lam w)) _ = _
    rw [← push_push, ih _ hvw, site_step_outside G hlam _ hvu]

lemma q_power (lam : ℝ) (hlam : 0 < lam) (k : ℕ) :
    (1-p lam)^k = (1+lam)^(-(k:ℝ)) := by
  have hq : 1-p lam = 1/(1+lam) := by unfold p; field_simp <;> ring
  rw [hq, Real.rpow_neg (by positivity), Real.rpow_natCast, one_div_pow]
  simp only [one_div]

lemma second_sweep_marginal (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν)
    (w₁ w₂ : List V) (h₁ : IsSweep Finset.univ w₁) (h₂ : IsSweep Finset.univ w₂) (v : V) :
    p lam * (1+lam)^(-(G.degree v:ℝ)) ≤
      expectation (push ν (word G lam (w₁++w₂))) (fun σ => if σ.val v = true then 1 else 0) := by
  classical
  have hmem : v ∈ w₂ := by
    rw [← List.mem_toFinset, h₂.2]
    exact Finset.mem_univ _
  obtain ⟨pre,post,hw⟩ := List.mem_iff_append.mp hmem
  have hpost : v ∉ post := by
    have hh := h₂.1
    rw [hw] at hh
    exact (List.nodup_cons.mp (List.nodup_append.mp hh).2.1).1
  have he : w₁++w₂ = ((w₁++pre)++[v])++post := by rw [hw]; simp [List.append_assoc]
  rw [he, word_append, ← push_push, site_word_outside G hlam _ post hpost,
    word_append, ← push_push]
  simp only [word, List.map_singleton, List.prod_singleton]
  rw [expected_site_occupancy G hlam]
  have hcover : G.neighborFinset v ⊆ (w₁++pre).toFinset := by
    intro u hu
    simp [List.toFinset_append, h₁.2]
  have hh := emptyOn_word_lower G hlam ν hν (w₁++pre) (G.neighborFinset v) hcover
  have hevent : emptyOn G (G.neighborFinset v) =
      (fun σ : State G => if nbrSize G v σ.val = 0 then (1:ℝ) else 0) := by
    ext σ
    simp only [emptyOn, nbrSize_zero]
  rw [hevent, q_power lam hlam] at hh
  exact mul_le_mul_of_nonneg_left hh (p_pos hlam).le

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma stochastic_mul {Ω : Type} [Fintype Ω] {K L : Matrix Ω Ω ℝ}
    (hK : MarkovMixing.IsStochastic K) (hL : MarkovMixing.IsStochastic L) :
    MarkovMixing.IsStochastic (K*L) := by
  constructor
  · intro x y
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (hK.1 x z) (hL.1 z y))
  · intro x
    change (∑ y, ∑ z, K x z*L z y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hL.2, mul_one]
    exact hK.2 x

lemma stochastic_pow {Ω : Type} [Fintype Ω] [DecidableEq Ω] {K : Matrix Ω Ω ℝ}
    (hK : MarkovMixing.IsStochastic K) (T : ℕ) : MarkovMixing.IsStochastic (K^T) := by
  induction T with
  | zero =>
    constructor
    · intro x y
      simp only [pow_zero, Matrix.one_apply]
      split_ifs <;> norm_num
    · intro x; simp [Matrix.one_apply]
  | succ T ih => rw [pow_succ]; exact stochastic_mul ih hK

lemma point_push {Ω : Type} [Fintype Ω] [DecidableEq Ω] (x : Ω) (K : Matrix Ω Ω ℝ) :
    push (point x) K = fun y => K x y := by
  ext y
  simp [push, point, Matrix.vecMul, dotProduct]

variable {V : Type} [Fintype V] [DecidableEq V]

lemma size_larger (G : SimpleGraph V) (I J : State G) :
    size (larger G I J).val = max (size I.val) (size J.val) := by
  unfold larger
  split_ifs with h
  · exact (max_eq_right h.le).symm
  · exact (max_eq_left (le_of_not_gt h)).symm

lemma record_stochastic [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) : MarkovMixing.IsStochastic (recordKernel G lam) := by
  have hK := scan_stochastic G hlam
  constructor
  · intro x y
    unfold recordKernel
    split_ifs
    · exact hK.1 _ _
    · rfl
  · intro x
    rw [Fintype.sum_prod_type]
    simp only [recordKernel]
    simp_rw [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hK.2 x.1

lemma runLargest_dist [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (I : State G) (T : ℕ) :
    MarkovMixing.IsDist (runLargest G lam I T) := by
  have hK := stochastic_pow (record_stochastic G hlam) T
  constructor
  · intro B
    exact Finset.sum_nonneg (fun J _ => hK.1 (I,I) (J,B))
  · change (∑ B, ∑ J, (recordKernel G lam^T) (I,I) (J,B)) = 1
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]
    exact hK.2 (I,I)

lemma repetition_stochastic [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (I : State G) (T : ℕ) :
    MarkovMixing.IsStochastic (repetitionKernel G lam I T) := by
  have hrun := runLargest_dist G hlam I T
  constructor
  · intro B C
    unfold repetitionKernel
    apply Finset.sum_nonneg
    intro A _
    split_ifs
    · exact hrun.1 A
    · rfl
  · intro B
    unfold repetitionKernel
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hrun.2

lemma amplified_dist [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (I : State G) (T R : ℕ) :
    MarkovMixing.IsDist (amplifiedLaw G lam I T R) := by
  exact push_dist (by
    constructor
    · intro J; unfold point; split_ifs <;> norm_num
    · simp [point]) (stochastic_pow (repetition_stochastic G hlam I T) R)

lemma record_row_average (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (x : State G × State G) (f : State G × State G → ℝ) :
    (∑ y, recordKernel G lam x y*f y) = ∑ J, K G lam x.1 J*f (J,larger G x.2 J) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [recordKernel, ite_mul, zero_mul]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma record_first_step (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (ν : State G × State G → ℝ) (f : State G → ℝ) :
    expectation (push ν (recordKernel G lam)) (fun x => f x.1) =
      expectation ν (fun x => ∑ J, K G lam x.1 J*f J) := by
  rw [expectation_push]
  simp_rw [record_row_average]
  rfl

lemma record_first_expectation (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (x : State G × State G) (T : ℕ) (f : State G → ℝ) :
    expectation (push (point x) (recordKernel G lam^T)) (fun y => f y.1) =
      expectation (push (point x.1) (K G lam^T)) f := by
  induction T generalizing f with
  | zero => simp [push, point, expectation]
  | succ T ih =>
    rw [pow_succ, ← push_push, record_first_step]
    rw [ih (fun I => ∑ J, K G lam I J*f J)]
    conv_rhs => rw [pow_succ, ← push_push, expectation_push]
    rfl

lemma record_step_increases [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (ν : State G × State G → ℝ) (hν : MarkovMixing.IsDist ν) :
    expectation ν (fun x => (size x.2.val:ℝ)) ≤
      expectation (push ν (recordKernel G lam)) (fun x => (size x.2.val:ℝ)) := by
  have hK := scan_stochastic G hlam
  rw [expectation_push]
  simp_rw [record_row_average]
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hν.1 x)
  calc
    _ = ∑ J, K G lam x.1 J*(size x.2.val:ℝ) := by rw [← Finset.sum_mul, hK.2, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro J _
      apply mul_le_mul_of_nonneg_left _ (hK.1 x.1 J)
      exact_mod_cast (show size x.2.val ≤ size (larger G x.2 J).val by rw [size_larger]; exact le_max_left _ _)

lemma record_step_dominates [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (ν : State G × State G → ℝ) (hν : MarkovMixing.IsDist ν) :
    expectation (push ν (recordKernel G lam)) (fun x => (size x.1.val:ℝ)) ≤
      expectation (push ν (recordKernel G lam)) (fun x => (size x.2.val:ℝ)) := by
  have hK := scan_stochastic G hlam
  rw [expectation_push, expectation_push]
  simp_rw [record_row_average]
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hν.1 x)
  apply Finset.sum_le_sum
  intro J _
  apply mul_le_mul_of_nonneg_left _ (hK.1 x.1 J)
  exact_mod_cast (show size J.val ≤ size (larger G x.2 J).val by rw [size_larger]; exact le_max_right _ _)

lemma runLargest_expectation (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : State G) (T : ℕ) :
    expectation (runLargest G lam I T) (fun J => size J.val) =
      expectation (push (point (I,I)) (recordKernel G lam^T)) (fun x => size x.2.val) := by
  rw [point_push]
  unfold expectation runLargest
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Fintype.sum_prod_type]

lemma record_time_domination [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (I : State G) (T : ℕ) (hT : 1 ≤ T) :
    timeMean G lam (point I) T ≤ expectation (runLargest G lam I T) (fun J => size J.val) := by
  let μ (j : ℕ) := push (point (I,I)) (recordKernel G lam^j)
  have hμ (j : ℕ) : MarkovMixing.IsDist (μ j) :=
    push_dist (point_dist (I,I)) (stochastic_pow (record_stochastic G hlam) j)
  have hsucc (j : ℕ) : μ (j+1) = push (μ j) (recordKernel G lam) := by
    dsimp [μ]
    rw [pow_succ, push_push]
  have hmono : Monotone (fun j => expectation (μ j) (fun x => (size x.2.val:ℝ))) := by
    apply monotone_nat_of_le_succ
    intro j
    rw [hsucc]
    exact record_step_increases G hlam (μ j) (hμ j)
  have hdom (j : ℕ) : expectation (push (point I) (K G lam^j)) (fun J => size J.val) ≤
      expectation (μ j) (fun x => size x.2.val) := by
    rw [← record_first_expectation G lam (I,I)]
    cases j with
    | zero => simp [μ, push, expectation, point]
    | succ j =>
      change expectation (μ (j+1)) _ ≤ expectation (μ (j+1)) _
      rw [hsucc]
      exact record_step_dominates G hlam _ (hμ j)
  have hrow (j : ℕ) (hj : j ∈ Finset.range T) :
      expectation (push (point I) (K G lam^j)) (fun J => size J.val) ≤
        expectation (runLargest G lam I T) (fun J => size J.val) := by
    rw [runLargest_expectation]
    exact (hdom j).trans (hmono (Finset.mem_range.mp hj).le)
  unfold timeMean
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  apply (div_le_iff₀ hTpos).mpr
  have hh := Finset.sum_le_sum (s := Finset.range T) hrow
  simpa [mul_comm] using hh

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

def failure (G : SimpleGraph V) [DecidableRel G.Adj] (ν : State G → ℝ) (a : ℝ) : ℝ :=
  expectation ν (fun I => if (size I.val:ℝ) < a then 1 else 0)

lemma success_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) (a : ℝ) : 0 ≤ success G ν a := by
  unfold success
  apply Finset.sum_nonneg
  intro I _
  split_ifs
  · exact hν.1 I
  · rfl

lemma success_le_one (G : SimpleGraph V) [DecidableRel G.Adj] {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) (a : ℝ) : success G ν a ≤ 1 := by
  calc
    _ ≤ ∑ I, ν I := by
      apply Finset.sum_le_sum
      intro I _
      split_ifs
      · rfl
      · exact hν.1 I
    _ = _ := hν.2

lemma success_add_failure (G : SimpleGraph V) [DecidableRel G.Adj] {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) (a : ℝ) : success G ν a+failure G ν a = 1 := by
  unfold success failure expectation
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ I, ν I := by
      apply Finset.sum_congr rfl
      intro I _
      by_cases h : a ≤ (size I.val:ℝ)
      · simp [h, not_lt.mpr h]
      · simp [h, lt_of_not_ge h]
    _ = _ := hν.2

lemma size_le_card (G : SimpleGraph V) (I : State G) : size I.val ≤ Fintype.card V :=
  Finset.card_filter_le _ _

lemma expectation_size_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    {ν : State G → ℝ} (hν : MarkovMixing.IsDist ν) {a : ℝ} (ha : 0 ≤ a) :
    expectation ν (fun I => size I.val) ≤ a+Fintype.card V*success G ν a := by
  have hh (I : State G) : (size I.val:ℝ) ≤ a+(if a ≤ (size I.val:ℝ) then (Fintype.card V:ℝ) else 0) := by
    split_ifs with h
    · have hsize : (size I.val:ℝ) ≤ Fintype.card V := by exact_mod_cast size_le_card G I
      linarith
    · have hh := lt_of_not_ge h
      linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun I _ => mul_le_mul_of_nonneg_left (hh I) (hν.1 I))
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul] at hs
  rw [hν.2, one_mul] at hs
  have he : (∑ I, ν I*(if a ≤ (size I.val:ℝ) then (Fintype.card V:ℝ) else 0)) =
      Fintype.card V*success G ν a := by
    unfold success
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    split_ifs <;> ring
  rw [he] at hs
  exact hs

lemma run_success_from_mean [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam Γ ε : ℝ} (hlam : 0 < lam) (hΓ : 0 < Γ) (hε : 0 < ε) (hε1 : ε < 1)
    (I : State G) (T : ℕ) (hT : 1 ≤ T)
    (hmean : (1-ε/2)*Fintype.card V/Γ ≤ timeMean G lam (point I) T) :
    ε/(2*Γ) ≤ success G (runLargest G lam I T) ((1-ε)*Fintype.card V/Γ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have ha : 0 ≤ (1-ε)*Fintype.card V/Γ := by positivity
  have hup := expectation_size_upper G (runLargest_dist G hlam I T) ha
  have hlo := hmean.trans (record_time_domination G hlam I T hT)
  have heq : (1-ε)*Fintype.card V/Γ + (ε/(2*Γ))*Fintype.card V =
      (1-ε/2)*Fintype.card V/Γ := by ring
  have hh : (ε/(2*Γ))*Fintype.card V ≤
      success G (runLargest G lam I T) ((1-ε)*Fintype.card V/Γ)*Fintype.card V := by nlinarith
  exact (mul_le_mul_iff_left₀ hN).mp hh

lemma repetition_row_average (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : State G) (T : ℕ) (B : State G) (f : State G → ℝ) :
    (∑ C, repetitionKernel G lam I T B C*f C) = ∑ A, runLargest G lam I T A*f (larger G B A) := by
  classical
  unfold repetitionKernel
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma failure_step (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : State G) (T : ℕ) (ν : State G → ℝ) (a : ℝ) :
    failure G (push ν (repetitionKernel G lam I T)) a = failure G ν a*failure G (runLargest G lam I T) a := by
  classical
  unfold failure
  rw [expectation_push]
  simp_rw [repetition_row_average]
  have he (B A : State G) : (if (size (larger G B A).val:ℝ) < a then (1:ℝ) else 0) =
      (if (size B.val:ℝ) < a then 1 else 0)*(if (size A.val:ℝ) < a then 1 else 0) := by
    rw [size_larger, Nat.cast_max]
    by_cases hB : (size B.val:ℝ) < a <;> by_cases hA : (size A.val:ℝ) < a <;>
      simp [max_lt_iff, hB, hA]
  simp_rw [he]
  have he' (B : State G) : (∑ A, runLargest G lam I T A *
      ((if (size B.val:ℝ) < a then 1 else 0)*(if (size A.val:ℝ) < a then 1 else 0))) =
      (if (size B.val:ℝ) < a then 1 else 0)*expectation (runLargest G lam I T) (fun A => if (size A.val:ℝ) < a then 1 else 0) := by
    unfold expectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    ring
  simp_rw [he', ← mul_assoc, ← Finset.sum_mul]
  rfl

lemma failure_power (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : State G) (T R : ℕ) (ν : State G → ℝ) (a : ℝ) :
    failure G (push ν (repetitionKernel G lam I T^R)) a =
      failure G ν a*(failure G (runLargest G lam I T) a)^R := by
  induction R with
  | zero => simp [push]
  | succ R ih => rw [pow_succ, ← push_push, failure_step, ih, pow_succ]; ring

lemma failure_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) (a : ℝ) : 0 ≤ failure G ν a := by
  unfold failure expectation
  apply Finset.sum_nonneg
  intro I _
  exact mul_nonneg (hν.1 I) (by dsimp only; split_ifs <;> norm_num)

lemma failure_le_one (G : SimpleGraph V) [DecidableRel G.Adj] {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) (a : ℝ) : failure G ν a ≤ 1 := by
  have hh := success_add_failure G hν a
  have hs := success_nonneg G hν a
  linarith

lemma amplification_bound [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (I : State G) (T R : ℕ) {a q : ℝ}
    (hq : q ≤ success G (runLargest G lam I T) a) :
    1-Real.exp (-q*R) ≤ success G (amplifiedLaw G lam I T R) a := by
  have hr := runLargest_dist G hlam I T
  have hp := point_dist I
  have hpow : failure G (runLargest G lam I T) a ^ R ≤ Real.exp (-q*R) := by
    have hf : failure G (runLargest G lam I T) a ≤ Real.exp (-q) := by
      have hs := success_add_failure G hr a
      have he := Real.one_sub_le_exp_neg q
      linarith
    calc
      _ ≤ (Real.exp (-q))^R := pow_le_pow_left₀ (failure_nonneg G hr a) hf R
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hb : failure G (amplifiedLaw G lam I T R) a ≤ Real.exp (-q*R) := by
    unfold amplifiedLaw
    rw [failure_power]
    calc
      _ ≤ 1*(failure G (runLargest G lam I T) a)^R :=
        mul_le_mul_of_nonneg_right (failure_le_one G hp a) (pow_nonneg (failure_nonneg G hr a) R)
      _ ≤ _ := by simpa using hpow
  have hs := success_add_failure G (amplified_dist G hlam I T R) a
  linarith

lemma computed_repetition_bound [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℕ} {lam c ε δ : ℝ} (hlam : 0 < lam) (hΓ : 0 < Gamma Δ lam c)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (I : State G) (T : ℕ) {a : ℝ}
    (hs : ε/(2*Gamma Δ lam c) ≤ success G (runLargest G lam I T) a) :
    1-δ ≤ success G (amplifiedLaw G lam I T (repeats Δ lam c ε δ)) a := by
  let q := ε/(2*Gamma Δ lam c)
  have hq : 0 < q := by dsimp [q]; positivity
  have hceil : (2*Gamma Δ lam c/ε)*Real.log (1/δ) ≤ (repeats Δ lam c ε δ:ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
  have hprod : Real.log (1/δ) ≤ q*(repeats Δ lam c ε δ) := by
    have hh := mul_le_mul_of_nonneg_left hceil hq.le
    dsimp [q] at hh ⊢
    calc
      _ = (ε/(2*Gamma Δ lam c))*((2*Gamma Δ lam c/ε)*Real.log (1/δ)) := by field_simp <;> ring
      _ ≤ _ := hh
  have hexp : Real.exp (-q*(repeats Δ lam c ε δ)) ≤ δ := by
    calc
      _ ≤ Real.exp (-Real.log (1/δ)) := Real.exp_le_exp.mpr (by linarith)
      _ = δ := by rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  have hh := amplification_bound G hlam I T (repeats Δ lam c ε δ) hs
  linarith

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma weight_product (lam : ℝ) (σ : V → Bool) :
    lam ^ size σ = ∏ v, if σ v = true then lam else 1 := by
  simp [size, Finset.prod_ite]

lemma partition_upper (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) :
    (∑ σ : V → Bool, MarkovMixing.hardcoreWeight G lam σ) ≤ (1+lam) ^ Fintype.card V := by
  calc
    _ ≤ ∑ σ : V → Bool, lam ^ size σ := by
      apply Finset.sum_le_sum
      intro σ _
      unfold MarkovMixing.hardcoreWeight
      split_ifs
      · rfl
      · exact (pow_pos hlam _).le
    _ = _ := by
      simp_rw [weight_product]
      calc
        _ = ∏ _ : V, ∑ b : Bool, if b = true then lam else 1 :=
          (Fintype.prod_sum (fun (_ : V) (b : Bool) => if b = true then lam else 1)).symm
        _ = _ := by simp [Fintype.sum_bool, add_comm]

lemma hcLaw_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) :
    (min 1 lam) ^ Fintype.card V / (1+lam) ^ Fintype.card V ≤
      HardCoreBochner.hcLaw G lam σ := by
  have hn : min 1 lam ^ Fintype.card V ≤ lam ^ size σ.val := by
    rw [weight_product]
    calc
      _ = ∏ _ : V, min 1 lam := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intro _ _; exact le_min (by norm_num) hlam.le
        · intro v _
          split_ifs
          · exact min_le_right _ _
          · exact min_le_left _ _
  change _ ≤ MarkovMixing.hardcoreWeight G lam σ.val / _
  rw [MarkovMixing.hardcoreWeight, if_pos σ.property]
  exact div_le_div₀ (pow_pos hlam _).le hn
    (hcPartition_pos G hlam) (partition_upper G hlam)

lemma hcLaw_log_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) :
    -entropyBound (Fintype.card V) lam ≤ Real.log (HardCoreBochner.hcLaw G lam σ) := by
  have hm : 0 < min 1 lam := lt_min (by norm_num) hlam
  have hp : 0 < 1 + lam := by positivity
  have h := Real.log_le_log (div_pos (pow_pos hm _) (pow_pos hp _)) (hcLaw_lower G hlam σ)
  rw [Real.log_div (pow_pos hm _).ne' (pow_pos hp _).ne', Real.log_pow, Real.log_pow] at h
  unfold entropyBound
  rw [Real.log_div hp.ne' hm.ne']
  linarith

lemma initial_entropy_bound (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) {ν : State G → ℝ} (hν : MarkovMixing.IsDist ν) :
    kl ν (HardCoreBochner.hcLaw G lam) ≤ entropyBound (Fintype.card V) lam := by
  classical
  rw [kl_eq_sum]
  calc
    _ ≤ ∑ σ, ν σ * entropyBound (Fintype.card V) lam := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hz : ν σ = 0
      · simp [hz]
      · have hn : 0 < ν σ := lt_of_le_of_ne (hν.1 σ) (Ne.symm hz)
        have hle : ν σ ≤ 1 := by
          rw [← hν.2]
          exact Finset.single_le_sum (fun (x : State G) _ => hν.1 x) (Finset.mem_univ σ)
        apply mul_le_mul_of_nonneg_left _ hn.le
        rw [Real.log_div hn.ne' (hcLaw_pos G hlam σ).ne']
        have hlν : Real.log (ν σ) ≤ 0 := Real.log_nonpos hn.le hle
        have hlπ := hcLaw_log_lower G hlam σ
        linarith
    _ = _ := by rw [← Finset.sum_mul, hν.2, one_mul]

lemma mul_log_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log (x/y) = x * Real.log x - x * Real.log y := by
  by_cases hz : x = 0
  · simp [hz]
  · rw [Real.log_div hz hy.ne']; ring

lemma kl_mixture {Ω U : Type} [Fintype Ω] [Fintype U]
    (π : Ω → ℝ) (hπ : ∀ x, 0 < π x) (μ : U → Ω → ℝ)
    (hμ : ∀ u x, 0 ≤ μ u x) (w : U → ℝ) (hw : ∀ u, 0 ≤ w u) (hs : ∑ u, w u = 1) :
    kl (fun x => ∑ u, w u * μ u x) π ≤ ∑ u, w u * kl (μ u) π := by
  classical
  simp_rw [kl_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hm : 0 ≤ ∑ u, w u * μ u x :=
    Finset.sum_nonneg (fun u _ => mul_nonneg (hw u) (hμ u x))
  rw [mul_log_div hm (hπ x)]
  have hj := Real.convexOn_mul_log.map_sum_le (t := Finset.univ)
    (w := w) (p := fun u => μ u x) (fun u _ => hw u) hs (fun u _ => hμ u x)
  simp only [smul_eq_mul] at hj
  calc
    _ ≤ (∑ u, w u * (μ u x * Real.log (μ u x))) - (∑ u, w u * μ u x) * Real.log (π x) :=
      sub_le_sub_right hj _
    _ = _ := by
      simp_rw [mul_log_div (hμ _ x) (hπ x), mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
      rw [Finset.sum_mul]

lemma push_scan [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (ν : State G → ℝ) (σ : State G) :
    push ν (K G lam) σ = (Fintype.card V : ℝ)⁻¹ * ∑ u, push ν (P G lam u) σ := by
  rw [scan_eq]
  change (∑ τ, ν τ * ((Fintype.card V : ℝ)⁻¹ • ∑ u, P G lam u) τ σ) = _
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  change (∑ τ, ν τ * ((Fintype.card V : ℝ)⁻¹ * P G lam u τ σ)) =
    (Fintype.card V : ℝ)⁻¹ * ∑ τ, ν τ * P G lam u τ σ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

lemma scan_entropy_drop [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) {ν : State G → ℝ} (hν : MarkovMixing.IsDist ν) :
    (2 / (Fintype.card V : ℝ)) * ∑ u, tv ν (push ν (P G lam u)) ^ 2 ≤
      kl ν (HardCoreBochner.hcLaw G lam) - kl (push ν (K G lam)) (HardCoreBochner.hcLaw G lam) := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hw : (∑ _ : V, (Fintype.card V : ℝ)⁻¹) = 1 := by simp [hn.ne']
  have hm := kl_mixture (HardCoreBochner.hcLaw G lam) (hcLaw_pos G hlam)
    (fun u => push ν (P G lam u))
    (fun u x => (push_dist hν (heatBath_stochastic G hlam {u})).1 x)
    (fun _ => (Fintype.card V : ℝ)⁻¹) (fun _ => inv_nonneg.mpr hn.le) hw
  have hm0 : (fun x => ∑ u, (Fintype.card V : ℝ)⁻¹ * push ν (P G lam u) x) = push ν (K G lam) := by
    ext x
    rw [← Finset.mul_sum, push_scan]
  rw [hm0, ← Finset.mul_sum] at hm
  have hloc (u : V) :
      2 * tv ν (push ν (P G lam u)) ^ 2 ≤
        kl ν (HardCoreBochner.hcLaw G lam) - kl (push ν (P G lam u)) (HardCoreBochner.hcLaw G lam) := by
    have hh := (LocalOccupancyIS.Glauber.lemma_7 G lam hlam u ν hν).2.2
      (P G lam u) (by simp)
    rw [hh.2.2.1]
    exact hh.2.2.2
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hloc u)
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [← Finset.mul_sum] at hsum
  have hsum' := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
  have hcancel : (Fintype.card V : ℝ)⁻¹ * Fintype.card V = 1 := inv_mul_cancel₀ hn.ne'
  calc
    _ = (Fintype.card V : ℝ)⁻¹ * (2 * ∑ u, tv ν (push ν (P G lam u)) ^ 2) := by ring
    _ ≤ _ := hsum'
    _ = kl ν (HardCoreBochner.hcLaw G lam) - (Fintype.card V : ℝ)⁻¹ *
        ∑ u, kl (push ν (P G lam u)) (HardCoreBochner.hcLaw G lam) := by
      rw [mul_sub, ← mul_assoc, hcancel, one_mul]
    _ ≤ _ := sub_le_sub_left hm _

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma score_range (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ} (hΔ : DegreeBound G Δ)
    {lam β γ : ℝ} (hlam : 0 < lam) (hβ : 0 < β) (hγ : 0 < γ) (u : V) (σ : State G) :
    0 ≤ score G lam β γ u σ ∧ score G lam β γ u σ ≤ max (β*p lam) (γ*Δ) := by
  have hp : 0 < p lam := div_pos hlam (by positivity)
  have hn : nbrSize G u σ.val ≤ Δ :=
    (Finset.card_filter_le _ _).trans (hΔ u)
  unfold score
  by_cases hz : nbrSize G u σ.val = 0
  · simp only [hz, ite_true, Nat.cast_zero, mul_one, mul_zero, add_zero]
    exact ⟨(mul_pos hβ hp).le, le_max_left _ _⟩
  · simp only [if_neg hz, mul_zero, zero_add]
    exact ⟨mul_nonneg hγ.le (Nat.cast_nonneg _),
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hγ.le).trans (le_max_right _ _)⟩

lemma score_expectation (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (β γ : ℝ) (ν : State G → ℝ) (u : V) :
    expectation ν (score G lam β γ u) =
      β * expectation (push ν (P G lam u)) (fun σ => if σ.val u = true then 1 else 0) +
      γ * expectation ν (fun σ => nbrSize G u σ.val) := by
  rw [expected_site_occupancy G hlam]
  unfold expectation score
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro σ _ <;> ring

lemma score_compare (G : SimpleGraph V) [DecidableRel G.Adj] {lam β γ : ℝ}
    (hlam : 0 < lam) (hβ : 0 < β) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) (u : V) :
    expectation ν (score G lam β γ u) ≤
      β * expectation ν (fun σ => if σ.val u = true then 1 else 0) +
      γ * expectation ν (fun σ => nbrSize G u σ.val) + β * tv ν (push ν (P G lam u)) := by
  have hh := expectation_tv (push_dist hν (heatBath_stochastic G hlam {u})) hν
    (fun σ => if σ.val u = true then (1 : ℝ) else 0)
    (L := 1) (fun σ => by split_ifs <;> norm_num)
  rw [tv_symm, one_mul] at hh
  have hh' := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hh) hβ.le
  rw [score_expectation G hlam β γ]
  simp only [P] at *
  linarith

lemma sum_expected_occupancy (G : SimpleGraph V) [DecidableRel G.Adj] (ν : State G → ℝ) :
    (∑ u, expectation ν (fun σ => if σ.val u = true then (1 : ℝ) else 0)) =
      expectation ν (fun σ => size σ.val) := by
  unfold expectation
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← size_sum]

lemma sum_expected_neighbors (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : DegreeBound G Δ) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) :
    (∑ u, expectation ν (fun σ => nbrSize G u σ.val)) ≤
      Δ * expectation ν (fun σ => size σ.val) := by
  unfold expectation
  rw [Finset.sum_comm, Finset.mul_sum]
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hh := mul_le_mul_of_nonneg_left (degree_sum_bound G hΔ σ.val) (hν.1 σ)
  convert hh using 1 <;> ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma list_sum_counts (a : V → ℝ) (w : List V) :
    (w.map a).sum = ∑ v, (w.count v : ℝ) * a v := by
  rw [Finset.sum_list_map_count]
  simp only [nsmul_eq_mul]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  have hm : v ∉ w := by simpa using hv
  simp [List.count_eq_zero.mpr hm]

lemma list_take_sum_le (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) (w : List V) (j : ℕ) :
    ((w.take j).map a).sum ≤ (w.map a).sum := by
  rw [list_sum_counts, list_sum_counts]
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_right _ (ha v)
  exact_mod_cast List.Sublist.count_le v (List.take_sublist j w)

lemma total_word_sum_le (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) (w : V → List V) :
    (∑ u, ((w u).map a).sum) ≤ occurrences w * ∑ v, a v := by
  simp_rw [list_sum_counts]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (ha v)
  have h : (∑ u, (w u).count v) ≤ occurrences w :=
    Finset.le_sup (f := fun v => ∑ u, (w u).count v) (Finset.mem_univ v)
  exact_mod_cast h

lemma word_score_upper (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : DegreeBound G Δ) {lam β γ : ℝ} (hlam : 0 < lam) (hβ : 0 < β) (hγ : 0 < γ)
    (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) (u : V) (w : List V) :
    expectation (push ν (word G lam w)) (score G lam β γ u) ≤
      expectation ν (score G lam β γ u) +
      max (β*p lam) (γ*Δ) * (w.map (fun v => tv ν (push ν (P G lam v)))).sum := by
  have hL : 0 ≤ max (β*p lam) (γ*Δ) := le_trans
    (mul_nonneg hγ.le (Nat.cast_nonneg Δ)) (le_max_right _ _)
  have hh := expectation_tv (push_dist hν (word_stochastic G hlam w)) hν
    (score G lam β γ u) (score_range G hΔ hlam hβ hγ u)
  rw [tv_symm] at hh
  have ht := mul_le_mul_of_nonneg_left (tv_word_bound G hlam ν w) hL
  have hh' := le_trans (le_abs_self _) hh
  linarith

lemma certificate_compare (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : DegreeBound G Δ) {lam β γ η : ℝ} (hlam : 0 < lam) (hβ : 0 < β) (hγ : 0 < γ)
    (w : V → List V)
    (hc : WordCertificate G lam β γ η w ∨
      ∃ a : V → List ℕ, Prefixes w a ∧ PrefixCertificate G lam β γ η w a)
    (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) (u : V) :
    1-η ≤ expectation ν (score G lam β γ u) +
      max (β*p lam) (γ*Δ) * ((w u).map (fun v => tv ν (push ν (P G lam v)))).sum := by
  classical
  rcases hc with hc | ⟨a,ha,hc⟩
  · exact (hc ν hν u).trans (word_score_upper G hΔ hlam hβ hγ ν hν u (w u))
  · have hL : 0 ≤ max (β*p lam) (γ*Δ) := le_trans
      (mul_nonneg hγ.le (Nat.cast_nonneg Δ)) (le_max_right _ _)
    have hj (j : ℕ) :
        expectation (push ν (word G lam ((w u).take j))) (score G lam β γ u) ≤
          expectation ν (score G lam β γ u) +
          max (β*p lam) (γ*Δ) * ((w u).map (fun v => tv ν (push ν (P G lam v)))).sum := by
      refine (word_score_upper G hΔ hlam hβ hγ ν hν u ((w u).take j)).trans ?_
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (list_take_sum_le (fun v : V => tv ν (push ν (P G lam v)))
          (fun v => tv_nonneg ν (push ν (P G lam v))) (w u) j) hL)
    have hh := List.sum_le_card_nsmul ((a u).map (fun j =>
      expectation (push ν (word G lam ((w u).take j))) (score G lam β γ u)))
      (expectation ν (score G lam β γ u) +
        max (β*p lam) (γ*Δ) * ((w u).map (fun v => tv ν (push ν (P G lam v)))).sum)
      (by intro x hx; rcases List.mem_map.mp hx with ⟨j,_,rfl⟩; exact hj j)
    simp only [List.length_map, nsmul_eq_mul] at hh
    have hn : (0 : ℝ) < (a u).length := by exact_mod_cast (ha u).1
    exact (hc ν hν u).trans ((div_le_iff₀ hn).mpr (by simpa [mul_comm] using hh))

lemma certificate_global (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : DegreeBound G Δ) {lam β γ η : ℝ} (hlam : 0 < lam) (hβ : 0 < β) (hγ : 0 < γ)
    (w : V → List V)
    (hc : WordCertificate G lam β γ η w ∨
      ∃ a : V → List ℕ, Prefixes w a ∧ PrefixCertificate G lam β γ η w a)
    (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) :
    Fintype.card V * (1-η) ≤
      (β+γ*Δ) * expectation ν (fun σ => size σ.val) +
      transferConstant Δ (occurrences w) lam β γ * ∑ v, tv ν (push ν (P G lam v)) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun u _ =>
    (certificate_compare G hΔ hlam hβ hγ w hc ν hν u).trans
      (add_le_add (score_compare G (γ := γ) hlam hβ ν hν u) le_rfl))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [sum_expected_occupancy] at hs
  have hn := mul_le_mul_of_nonneg_left (sum_expected_neighbors G hΔ ν hν) hγ.le
  have hL : 0 ≤ max (β*p lam) (γ*Δ) := le_trans
    (mul_nonneg hγ.le (Nat.cast_nonneg Δ)) (le_max_right _ _)
  have hw := mul_le_mul_of_nonneg_left
    (total_word_sum_le (fun v => tv ν (push ν (P G lam v))) (fun v => tv_nonneg _ _) w) hL
  unfold transferConstant
  nlinarith

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma push_power_succ (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (ν : State G → ℝ) (j : ℕ) :
    push ν (K G lam ^ (j+1)) = push (push ν (K G lam ^ j)) (K G lam) := by
  rw [pow_succ, push_push]

lemma trajectory_dist [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) {ν : State G → ℝ} (hν : MarkovMixing.IsDist ν) (j : ℕ) :
    MarkovMixing.IsDist (push ν (K G lam ^ j)) := by
  induction j with
  | zero => simpa [push] using hν
  | succ j ih =>
    rw [push_power_succ]
    exact push_dist ih (scan_stochastic G hlam)

lemma entropy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) {ν : State G → ℝ} (hν : MarkovMixing.IsDist ν) :
    0 ≤ kl ν (HardCoreBochner.hcLaw G lam) := by
  have hh := finite_pinsker hν (hcLaw_dist G hlam) (fun σ _ => hcLaw_pos G hlam σ)
  nlinarith [sq_nonneg (tv ν (HardCoreBochner.hcLaw G lam))]

lemma time_tv_bound [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) {ν : State G → ℝ} (hν : MarkovMixing.IsDist ν)
    (T : ℕ) (hT : 1 ≤ T) :
    (∑ j ∈ Finset.range T, ∑ u, tv (push ν (K G lam ^ j))
      (push (push ν (K G lam ^ j)) (P G lam u))) ≤
    Fintype.card V * (T : ℝ) * Real.sqrt (kl ν (HardCoreBochner.hcLaw G lam) / (2*T)) := by
  classical
  let N : ℝ := Fintype.card V
  let H : ℝ := kl ν (HardCoreBochner.hcLaw G lam)
  let a (j : ℕ) (u : V) := tv (push ν (K G lam ^ j)) (push (push ν (K G lam ^ j)) (P G lam u))
  let h (j : ℕ) := kl (push ν (K G lam ^ j)) (HardCoreBochner.hcLaw G lam)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hH : 0 ≤ H := entropy_nonneg G hlam hν
  have hlast : 0 ≤ h T := entropy_nonneg G hlam (trajectory_dist G hlam hν T)
  have hzero : h 0 = H := by simp [h, H, push]
  have hdrop (j : ℕ) : (2/N) * ∑ u, a j u ^ 2 ≤ h j - h (j+1) := by
    simpa only [a, N, h, push_power_succ] using
      scan_entropy_drop G hlam (trajectory_dist G hlam hν j)
  have hsum := Finset.sum_le_sum (s := Finset.range T) (fun j _ => hdrop j)
  rw [← Finset.mul_sum, Finset.sum_range_sub', hzero] at hsum
  have hsum' : 2 * (∑ j ∈ Finset.range T, ∑ u, a j u ^ 2) ≤ N*H := by
    have hh := mul_le_mul_of_nonneg_left (hsum.trans (sub_le_self _ hlast)) hN.le
    calc
      _ = N * ((2/N) * ∑ j ∈ Finset.range T, ∑ u, a j u ^ 2) := by field_simp <;> ring
      _ ≤ _ := hh
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range T ×ˢ (Finset.univ : Finset V))
    (fun _ => (1 : ℝ)) (fun x => a x.1 x.2)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_product,
    Finset.card_range, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_mul,
    Finset.sum_product] at hc
  change (∑ j ∈ Finset.range T, ∑ u, a j u) ^ 2 ≤ (T : ℝ)*N*(∑ j ∈ Finset.range T, ∑ u, a j u ^ 2) at hc
  have hsq : (∑ j ∈ Finset.range T, ∑ u, a j u) ^ 2 ≤ N^2*T*H/2 := by
    have hh := mul_le_mul_of_nonneg_left hsum' (show 0 ≤ (T : ℝ)*N by positivity)
    nlinarith
  have hroot : 0 ≤ H/(2*T) := div_nonneg hH (by positivity)
  have heq : (N*(T:ℝ)*Real.sqrt (H/(2*T))) ^ 2 = N^2*T*H/2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hroot]
    field_simp
    <;> ring
  have hR : 0 ≤ N*(T:ℝ)*Real.sqrt (H/(2*T)) := by positivity
  change (∑ j ∈ Finset.range T, ∑ u, a j u) ≤ N*(T:ℝ)*Real.sqrt (H/(2*T))
  nlinarith

lemma transfer_time_bound [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ : DegreeBound G Δ) {lam β γ η : ℝ}
    (hlam : 0 < lam) (hβ : 0 < β) (hγ : 0 < γ) (w : V → List V)
    (hc : WordCertificate G lam β γ η w ∨
      ∃ a : V → List ℕ, Prefixes w a ∧ PrefixCertificate G lam β γ η w a)
    {ν : State G → ℝ} (hν : MarkovMixing.IsDist ν) (T : ℕ) (hT : 1 ≤ T) :
    timeMean G lam ν T ≥ Fintype.card V / (β+γ*Δ) *
      (1-η-transferConstant Δ (occurrences w) lam β γ *
        Real.sqrt (kl ν (HardCoreBochner.hcLaw G lam) / (2*T))) := by
  let Γ := β+γ*Δ
  let C := transferConstant Δ (occurrences w) lam β γ
  let r := Real.sqrt (kl ν (HardCoreBochner.hcLaw G lam) / (2*T))
  have hΓ : 0 < Γ := by dsimp [Γ]; positivity
  have hC : 0 ≤ C := by
    dsimp [C, transferConstant]
    have hL : 0 ≤ max (β*p lam) (γ*Δ) := le_trans
      (mul_nonneg hγ.le (Nat.cast_nonneg Δ)) (le_max_right _ _)
    positivity
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hs := Finset.sum_le_sum (s := Finset.range T) (fun j _ =>
    certificate_global G hΔ hlam hβ hγ w hc (push ν (K G lam ^ j)) (trajectory_dist G hlam hν j))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left (time_tv_bound G hlam hν T hT) hC
  change C * (∑ j ∈ Finset.range T, ∑ u, _) ≤ C * (Fintype.card V * (T:ℝ) * r) at ht
  have hb : (Fintype.card V : ℝ)*(T:ℝ)*(1-η-C*r) ≤
      Γ * ∑ j ∈ Finset.range T, expectation (push ν (K G lam ^ j)) (fun σ => size σ.val) := by
    change (T:ℝ)*(Fintype.card V*(1-η)) ≤ Γ * _ + C * _ at hs
    nlinarith
  change Fintype.card V / Γ * (1-η-C*r) ≤ _
  unfold timeMean
  apply (le_div_iff₀ hT').mpr
  apply (le_of_mul_le_mul_left (a := Γ) _ hΓ)
  calc
    _ = Fintype.card V*(T:ℝ)*(1-η-C*r) := by field_simp <;> ring
    _ ≤ _ := hb

lemma transfer_finite_bound [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ : DegreeBound G Δ) {lam β γ η : ℝ}
    (hlam : 0 < lam) (hβ : 0 < β) (hγ : 0 < γ) (w : V → List V)
    (hc : WordCertificate G lam β γ η w ∨
      ∃ a : V → List ℕ, Prefixes w a ∧ PrefixCertificate G lam β γ η w a)
    {ν : State G → ℝ} (hν : MarkovMixing.IsDist ν) (T : ℕ) (hT : 1 ≤ T)
    {ε : ℝ} (hε : 0 < ε)
    (horizon : (transferConstant Δ (occurrences w) lam β γ)^2 * entropyBound (Fintype.card V) lam / (2*ε^2) ≤ T) :
    timeMean G lam ν T ≥ (1-η-ε)*Fintype.card V/(β+γ*Δ) := by
  let C := transferConstant Δ (occurrences w) lam β γ
  have hC : 0 ≤ C := by
    dsimp [C, transferConstant]
    have hL : 0 ≤ max (β*p lam) (γ*Δ) := le_trans
      (mul_nonneg hγ.le (Nat.cast_nonneg Δ)) (le_max_right _ _)
    positivity
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hΓ : 0 < β+γ*Δ := by positivity
  have hH := entropy_nonneg G hlam hν
  have hHle := initial_entropy_bound G hlam hν
  have hr := Real.sq_sqrt (div_nonneg hH (by positivity : (0:ℝ) ≤ 2*T))
  have hsq : (C*Real.sqrt (kl ν (HardCoreBochner.hcLaw G lam)/(2*T)))^2 ≤ ε^2 := by
    have hh := (div_le_iff₀ (by positivity : (0:ℝ) < 2*ε^2)).mp horizon
    have hh' := mul_le_mul_of_nonneg_left hHle (sq_nonneg C)
    rw [mul_pow, hr, ← mul_div_assoc]
    change C^2 * entropyBound (Fintype.card V) lam ≤ (T:ℝ)*(2*ε^2) at hh
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*T)).mpr
    nlinarith
  have hroot : C*Real.sqrt (kl ν (HardCoreBochner.hcLaw G lam)/(2*T)) ≤ ε := by nlinarith
  have hscale : 0 ≤ (Fintype.card V : ℝ)/(β+γ*Δ) := div_nonneg (Nat.cast_nonneg _) hΓ.le
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub_left hroot (1-η)) hscale
  calc
    _ ≥ _ := transfer_time_bound G hΔ hlam hβ hγ w hc hν T hT
    _ ≥ _ := hh
    _ = _ := by ring

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma lambert_exists {x : ℝ} (hx : 0 ≤ x) : ∃ w : ℝ, 0 ≤ w ∧ w*Real.exp w = x := by
  have hc : ContinuousOn (fun w : ℝ => w*Real.exp w) (Set.Icc 0 x) := by fun_prop
  have h0 : (0:ℝ)*Real.exp 0 ≤ x := by simpa using hx
  have h1 : x ≤ x*Real.exp x := by
    have hh := Real.one_le_exp hx
    nlinarith
  have hi := intermediate_value_Icc hx hc
  obtain ⟨w,hw,he⟩ := hi ⟨h0,h1⟩
  exact ⟨w,hw.1,he⟩

lemma lambert_facts {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ RiskBalancingMNL.lambertW x ∧
      RiskBalancingMNL.lambertW x * Real.exp (RiskBalancingMNL.lambertW x) = x := by
  unfold RiskBalancingMNL.lambertW
  rw [dif_pos (lambert_exists hx)]
  exact Classical.choose_spec (lambert_exists hx)

lemma lambert_pos {x : ℝ} (hx : 0 < x) : 0 < RiskBalancingMNL.lambertW x := by
  have hh := lambert_facts hx.le
  rcases eq_or_lt_of_le hh.1 with he | he
  · rw [← he] at hh
    simp at hh
    linarith
  · exact he

lemma mul_exp_strictMonoOn : StrictMonoOn (fun w : ℝ => w*Real.exp w) (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  calc
    x*Real.exp x < y*Real.exp x := mul_lt_mul_of_pos_right hxy (Real.exp_pos _)
    _ ≤ y*Real.exp y := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxy.le) hy

lemma lambert_lt_of_lt {x D : ℝ} (hx : 0 ≤ x) (hD : 0 < D) (h : x < D*Real.exp D) :
    RiskBalancingMNL.lambertW x < D := by
  have hh := lambert_facts hx
  by_contra hn
  have hle : D ≤ RiskBalancingMNL.lambertW x := le_of_not_gt hn
  have hm := mul_exp_strictMonoOn.monotoneOn hD.le hh.1 hle
  rw [hh.2] at hm
  linarith

lemma gamma_optimizer_identity {Δ lam c : ℝ} (hΔ : 0 < Δ) (hlam : 0 < lam) (hc : 0 < c) :
    Gamma Δ lam c = Δ/(c*optimizer Δ lam c) := by
  have hp : 0 < p lam := div_pos hlam (by positivity)
  have hx : 0 < p lam*Δ/c := div_pos (mul_pos hp hΔ) hc
  have hz : 0 < optimizer Δ lam c := lambert_pos hx
  have he := (lambert_facts hx.le).2
  change optimizer Δ lam c * Real.exp (optimizer Δ lam c) = p lam*Δ/c at he
  have he' : Real.exp (optimizer Δ lam c) = p lam*Δ/(c*optimizer Δ lam c) := by
    apply (eq_div_iff (mul_ne_zero hc.ne' hz.ne')).mpr
    have hh := (eq_div_iff hc.ne').mp he
    nlinarith
  unfold Gamma beta gamma
  rw [he']
  field_simp
  <;> ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma sweep_words_neighborhood (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → List V) (hw : ∀ u, IsSweep (G.neighborFinset u) (w u)) :
    NeighborhoodWords G (threeWords w) := by
  intro u v hv
  have hm : v ∈ w u := by simpa [threeWords, List.mem_append] using hv
  have hh : v ∈ G.neighborFinset u := by rw [← (hw u).2]; simpa using hm
  simpa using hh

lemma sweep_occurrences (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ : DegreeBound G Δ) (w : V → List V)
    (hw : ∀ u, IsSweep (G.neighborFinset u) (w u)) : occurrences (threeWords w) ≤ 3*Δ := by
  unfold occurrences
  apply Finset.sup_le
  intro v _
  have he (u : V) : (threeWords w u).count v = 3*(if G.Adj v u then 1 else 0) := by
    simp only [threeWords, List.count_append, (hw u).1.count]
    have hh : v ∈ w u ↔ G.Adj v u := by
      rw [← List.mem_toFinset, (hw u).2, SimpleGraph.mem_neighborFinset]
      exact G.adj_comm u v
    simp only [hh]
    split_ifs <;> omega
  simp_rw [he, ← Finset.mul_sum]
  have hs : (∑ u, if G.Adj v u then 1 else 0) = G.degree v := by
    rw [← Finset.card_filter]
    congr 1
    ext u
    simp
  rw [hs]
  exact Nat.mul_le_mul_left 3 (hΔ v)

lemma three_prefixes (w : V → List V) : Prefixes (threeWords w) (threePrefixes w) := by
  intro u
  simp only [threePrefixes, threeWords, List.length_cons, List.length_nil, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false, List.length_append]
  constructor
  · norm_num
  · intro j hj
    rcases hj with rfl | rfl <;> omega

lemma finite_from_certificate [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ : DegreeBound G Δ) {lam c : ℝ}
    (hlam : 0 < lam) (hc : 0 < c) (w : V → List V)
    (hw : ∀ u, IsSweep (G.neighborFinset u) (w u))
    (hcert : PrefixCertificate G lam (beta lam (optimizer Δ lam c))
      (gamma c (optimizer Δ lam c)) 0 (threeWords w) (threePrefixes w)) :
    FiniteConclusion G Δ lam c w := by
  let z := optimizer Δ lam c
  let β := beta lam z
  let γ := gamma c z
  have hz : 0 ≤ z := (lambert_facts (div_nonneg (mul_nonneg (p_pos hlam).le (Nat.cast_nonneg Δ)) hc.le)).1
  have hβ : 0 < β := by dsimp [β, beta]; exact div_pos (Real.exp_pos _) (mul_pos (p_pos hlam) (by linarith))
  have hγ : 0 < γ := by dsimp [γ, gamma]; exact one_div_pos.mpr (mul_pos hc (by linarith))
  have hΓ : 0 < Gamma Δ lam c := by change 0 < β+γ*Δ; positivity
  have hocc := sweep_occurrences G hΔ w hw
  have hconst : transferConstant Δ (occurrences (threeWords w)) lam β γ ≤ cThree Δ lam c := by
    have hL : 0 ≤ max (β*p lam) (γ*Δ) := (mul_nonneg hγ.le (Nat.cast_nonneg Δ)).trans (le_max_right _ _)
    unfold transferConstant cThree
    change β+_ ≤ β+_
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ hL
    exact_mod_cast hocc
  have hC : 0 ≤ transferConstant Δ (occurrences (threeWords w)) lam β γ := by
    unfold transferConstant
    have hL : 0 ≤ max (β*p lam) (γ*Δ) := (mul_nonneg hγ.le (Nat.cast_nonneg Δ)).trans (le_max_right _ _)
    positivity
  have hH : 0 ≤ entropyBound (Fintype.card V) lam := by
    have hh := initial_entropy_bound G hlam (point_dist (⟨fun _ => false, by simp [MarkovMixing.IsHardcore]⟩ : State G))
    exact (entropy_nonneg G hlam (point_dist _)).trans hh
  have htime (I : State G) (ε : ℝ) (hε : 0 < ε) (T : ℕ) (hT : 1 ≤ T)
      (hh : cThree Δ lam c^2*entropyBound (Fintype.card V) lam/(2*ε^2) ≤ T) :
      (1-ε)*Fintype.card V/Gamma Δ lam c ≤ timeMean G lam (point I) T := by
    have hsq : (transferConstant Δ (occurrences (threeWords w)) lam β γ)^2 ≤ cThree Δ lam c^2 :=
      pow_le_pow_left₀ hC hconst 2
    have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hH) (by positivity : 0 ≤ 2*ε^2)
    have ht := transfer_finite_bound G hΔ hlam hβ hγ (threeWords w)
      (Or.inr ⟨threePrefixes w, three_prefixes w, hcert⟩) (point_dist I) T hT hε (hb.trans hh)
    simpa only [sub_zero, Gamma, β, γ, z] using ht
  refine ⟨hlam, hβ, hγ, hcert, hocc, ?_, ?_⟩
  · intro I ε hε _ T hT hh
    exact htime I ε hε T hT hh
  · intro I ε δ hε hε1 hδ hδ1
    dsimp only
    let T := horizon (Fintype.card V) Δ lam c ε
    have hT : 1 ≤ T := le_max_left _ _
    have hh : cThree Δ lam c^2*entropyBound (Fintype.card V) lam/(2*(ε/2)^2) ≤ T := by
      calc
        _ = 2*cThree Δ lam c^2*entropyBound (Fintype.card V) lam/ε^2 := by field_simp <;> ring
        _ ≤ _ := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
    have hs := run_success_from_mean G hlam hΓ hε hε1 I T hT (htime I (ε/2) (by linarith) T hT hh)
    exact ⟨amplified_dist G hlam I T _, hs, computed_repetition_bound G hlam hΓ hε hδ hδ1 I T hs⟩

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma scale_pos (t : ℕ) {b : ℝ} (hb : 0 ≤ b) : 0 < scale t b :=
  Real.rpow_pos_of_pos (by linarith) _

lemma scale_one_le {t : ℕ} (ht : 1 ≤ t) {b : ℝ} (hb : 0 ≤ b) : 1 ≤ scale t b := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hden : 0 < 2*(t:ℝ)-1 := by linarith
  unfold scale
  exact Real.one_le_rpow (by linarith) (by positivity)

lemma exp_D {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (hb : 0 ≤ b) :
    Real.exp (D Δ t b) = Δ/scale t b := by
  unfold D rho
  exact Real.exp_log (div_pos hΔ (scale_pos t hb))

lemma degree_scale_exp {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (hb : 0 ≤ b) :
    Δ = scale t b*Real.exp (D Δ t b) := by
  rw [exp_D hΔ hb]
  field_simp [(scale_pos t hb).ne']

lemma D_large_basic {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    8 ≤ D Δ t b ∧ 0 < D Δ t b ∧ 1 ≤ D Δ t b := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hh : 8 ≤ 8*Real.exp 1*t := by nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr ht')]
  constructor
  · exact hh.trans hD
  · constructor <;> linarith

lemma fugacity_pos {Δ b : ℝ} {t : ℕ} (hb : 0 ≤ b) (hD : 0 < D Δ t b) :
    0 < fugacity Δ t b := by
  unfold fugacity
  exact one_div_pos.mpr (mul_pos (scale_pos t hb) (pow_pos hD _))

lemma fugacity_le_inv_D {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 1 ≤ D Δ t b) : fugacity Δ t b ≤ 1/D Δ t b := by
  have hD0 : 0 < D Δ t b := by linarith
  have hr : 1 ≤ 2*t-1 := by omega
  have hp : D Δ t b ≤ D Δ t b^(2*t-1) := by
    exact le_self_pow₀ hD (by omega)
  have hs := scale_one_le ht hb
  have hden : D Δ t b ≤ scale t b*D Δ t b^(2*t-1) := by
    have hh := mul_le_mul_of_nonneg_right hs (pow_nonneg hD0.le (2*t-1))
    nlinarith
  exact div_le_div_of_nonneg_left (by norm_num) hD0 hden

lemma correction_exponent_bounds {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    0 ≤ 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b ∧
    4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b ≤ 2 := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hD0 := (D_large_basic ht hD).2.1
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hbase : 1 ≤ 4*Real.exp 1 := by linarith
  have hInv : 0 ≤ 1/(t:ℝ) := by positivity
  have hpow : (4*Real.exp 1)^(1-1/(t:ℝ)) ≤ 4*Real.exp 1 := by
    calc
      _ ≤ (4*Real.exp 1)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ = _ := Real.rpow_one _
  constructor
  · positivity
  · apply (div_le_iff₀ hD0).mpr
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4*(t:ℝ) by positivity)
    nlinarith

lemma correction_bounds {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    0 < correction Δ t b ∧ correction Δ t b ≤ 1 ∧
      (correction Δ t b)⁻¹ ≤ Real.exp 2 := by
  have hh := correction_exponent_bounds ht hD
  unfold correction
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr (by linarith)
  · rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)

lemma fugacity_degree {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (hb : 0 ≤ b) :
    fugacity Δ t b*Δ = Real.exp (D Δ t b)/D Δ t b^(2*t-1) := by
  conv_lhs =>
    rhs
    rw [degree_scale_exp (t := t) hΔ hb]
  unfold fugacity
  field_simp [(scale_pos t hb).ne']

lemma optimizer_bounds {Δ b : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    0 < optimizer Δ (fugacity Δ t b) (correction Δ t b) ∧
      optimizer Δ (fugacity Δ t b) (correction Δ t b) < D Δ t b := by
  have hΔ0 : 0 < Δ := by linarith
  have hD0 := (D_large_basic ht hD).2.1
  have hD1 := (D_large_basic ht hD).2.2
  have hlam := fugacity_pos hb hD0
  have hc := correction_bounds ht hD
  have hp : 0 < p (fugacity Δ t b) := div_pos hlam (by positivity)
  have hx : 0 < p (fugacity Δ t b)*Δ/correction Δ t b := div_pos (mul_pos hp hΔ0) hc.1
  constructor
  · exact lambert_pos hx
  · apply lambert_lt_of_lt hx.le hD0
    have hpLam : p (fugacity Δ t b) ≤ fugacity Δ t b := by
      unfold p
      exact div_le_self hlam.le (by linarith)
    have hpow : D Δ t b ≤ D Δ t b^(2*t-1) := le_self_pow₀ hD1 (by omega)
    have hLamDeg : fugacity Δ t b*Δ ≤ Real.exp (D Δ t b)/D Δ t b := by
      rw [fugacity_degree hΔ0 hb]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hD0 hpow
    have hxbound : p (fugacity Δ t b)*Δ/correction Δ t b ≤
        (Real.exp (D Δ t b)/D Δ t b)*Real.exp 2 := by
      rw [div_eq_mul_inv]
      have hpΔ := mul_le_mul_of_nonneg_right hpLam hΔ0.le
      exact mul_le_mul (hpΔ.trans hLamDeg) hc.2.2 (inv_nonneg.mpr hc.1.le)
        (div_nonneg (Real.exp_pos _).le hD0.le)
    have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
    have hDge : 8*Real.exp 1 ≤ D Δ t b := by
      have hh := mul_le_mul_of_nonneg_left ht' (show 0 ≤ 8*Real.exp 1 by positivity)
      linarith
    have he : 0 < Real.exp 1 := Real.exp_pos _
    have he2 : Real.exp 2 = (Real.exp 1)^2 := by
      rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add, pow_two]
    have hsq : Real.exp 2 < D Δ t b*D Δ t b := by rw [he2]; nlinarith
    have hratio : Real.exp 2/D Δ t b < D Δ t b := (div_lt_iff₀ hD0).mpr hsq
    calc
      _ ≤ _ := hxbound
      _ = Real.exp (D Δ t b)*(Real.exp 2/D Δ t b) := by ring
      _ < Real.exp (D Δ t b)*D Δ t b := mul_lt_mul_of_pos_left hratio (Real.exp_pos _)
      _ = _ := by ring

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma log_D_one_le {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) : 1 ≤ Real.log (D Δ t b) := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hh : Real.exp 1 ≤ D Δ t b := by nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 8*Real.exp 1) (sub_nonneg.mpr ht')]
  have hlog := Real.log_le_log he hh
  simpa only [Real.log_exp] using hlog

lemma optimizer_log_identity {Δ b : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    let z := optimizer Δ (fugacity Δ t b) (correction Δ t b)
    Real.log z+z = D Δ t b-((2*t-1:ℕ):ℝ)*Real.log (D Δ t b)-Real.log (1+fugacity Δ t b)+
      4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b := by
  dsimp only
  let lam := fugacity Δ t b
  let c := correction Δ t b
  let z := optimizer Δ lam c
  have hΔ0 : 0 < Δ := by linarith
  have hD0 := (D_large_basic ht hD).2.1
  have hlam : 0 < lam := fugacity_pos hb hD0
  have hc : 0 < c := (correction_bounds ht hD).1
  have hz : 0 < z := (optimizer_bounds hΔ ht hb hD).1
  have hp : 0 < p lam := div_pos hlam (by positivity)
  have he := (lambert_facts (div_pos (mul_pos hp hΔ0) hc).le).2
  change z*Real.exp z = p lam*Δ/c at he
  have hlog := congrArg Real.log he
  rw [Real.log_mul hz.ne' (Real.exp_pos z).ne', Real.log_exp] at hlog
  have hpEq : p lam*Δ/c = (Real.exp (D Δ t b)/D Δ t b^(2*t-1))/(1+lam)/c := by
    rw [← fugacity_degree hΔ0 hb]
    change (lam/(1+lam))*Δ/c = (lam*Δ)/(1+lam)/c
    ring
  rw [hpEq] at hlog
  rw [Real.log_div (div_pos (div_pos (Real.exp_pos _) (pow_pos hD0 _)) (by positivity)).ne' hc.ne',
    Real.log_div (div_pos (Real.exp_pos _) (pow_pos hD0 _)).ne' (by positivity),
    Real.log_div (Real.exp_pos _).ne' (pow_pos hD0 _).ne', Real.log_exp, Real.log_pow] at hlog
  have hcLog : Real.log c = -(4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b) := by
    exact Real.log_exp _
  rw [hcLog] at hlog
  simpa only [sub_neg_eq_add] using hlog

lemma optimizer_lower {Δ b : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    D Δ t b-3*(t:ℝ)*Real.log (D Δ t b) ≤
      optimizer Δ (fugacity Δ t b) (correction Δ t b) := by
  let lam := fugacity Δ t b
  let z := optimizer Δ lam (correction Δ t b)
  have hD0 := (D_large_basic ht hD).2.1
  have hD1 := (D_large_basic ht hD).2.2
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hlam : 0 < lam := fugacity_pos hb hD0
  have hz := optimizer_bounds hΔ ht hb hD
  have hlogz : Real.log z ≤ Real.log (D Δ t b) := Real.log_le_log hz.1 hz.2.le
  have hLam : lam ≤ 1/D Δ t b := fugacity_le_inv_D ht hb hD1
  have hlogLam : Real.log (1+lam) ≤ 1/D Δ t b := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+lam)
    linarith
  have ha := (correction_exponent_bounds ht hD).1
  have hlogD := log_D_one_le ht hD
  have hinv : 1/D Δ t b ≤ 1 := (div_le_one hD0).mpr hD1
  have htlog : 1 ≤ (t:ℝ)*Real.log (D Δ t b) := by nlinarith
  have he := optimizer_log_identity hΔ ht hb hD
  have hr : ((2*t-1:ℕ):ℝ) = 2*(t:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ 2*t)]; norm_num
  rw [hr] at he
  change Real.log z+z = _ at he
  change D Δ t b-3*(t:ℝ)*Real.log (D Δ t b) ≤ z
  nlinarith

lemma correction_exponent_relative {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    0 ≤ 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b ∧
      4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b ≤ 16*Real.exp 1*relativeError Δ t b := by
  have hD0 := (D_large_basic ht hD).2.1
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hlog := log_D_one_le ht hD
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hInv : 0 ≤ 1/(t:ℝ) := by positivity
  have hpow : (4*Real.exp 1)^(1-1/(t:ℝ)) ≤ 4*Real.exp 1 := by
    calc
      _ ≤ (4*Real.exp 1)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = _ := Real.rpow_one _
  refine ⟨(correction_exponent_bounds ht hD).1, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4*(t:ℝ) by positivity)
  have htlog : (t:ℝ) ≤ t*Real.log (D Δ t b) := by nlinarith
  have hm' := mul_le_mul_of_nonneg_left htlog (show 0 ≤ 16*Real.exp 1 by positivity)
  have hnum : 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ)) ≤ 16*Real.exp 1*((t:ℝ)*Real.log (D Δ t b)) := by nlinarith
  have hh := div_le_div_of_nonneg_right hnum hD0.le
  change _ ≤ 16*Real.exp 1*((t:ℝ)*Real.log (D Δ t b)/D Δ t b)
  calc
    _ ≤ (16*Real.exp 1*((t:ℝ)*Real.log (D Δ t b)))/D Δ t b := hh
    _ = _ := by ring

lemma quantitative_gamma_error {Δ b : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hsmall : relativeError Δ t b ≤ 1/(4*(16*Real.exp 1+3))) :
    |Gamma Δ (fugacity Δ t b) (correction Δ t b)*D Δ t b/Δ-1| ≤
      (4*(16*Real.exp 1+3))*relativeError Δ t b := by
  let d := D Δ t b
  let z := optimizer Δ (fugacity Δ t b) (correction Δ t b)
  let c := correction Δ t b
  let a := 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/d
  let e := relativeError Δ t b
  let C := 16*Real.exp 1+3
  let E := C*e
  have hd : 0 < d := (D_large_basic ht hD).2.1
  have hz : 0 < z := (optimizer_bounds hΔ ht hb hD).1
  have hzd : z ≤ d := (optimizer_bounds hΔ ht hb hD).2.le
  have hc : 0 < c := (correction_bounds ht hD).1
  have hc1 : c ≤ 1 := (correction_bounds ht hD).2.1
  have he : 0 ≤ e := by
    dsimp [e, relativeError]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith [log_D_one_le ht hD])) hd.le
  have hC : 0 < C := by dsimp [C]; positivity
  have hE : 0 ≤ E := mul_nonneg hC.le he
  have hEsmall : E ≤ 1/4 := by
    have hh := (le_div_iff₀ (show (0:ℝ) < 4*(16*Real.exp 1+3) by positivity)).mp hsmall
    change e*(4*C) ≤ 1 at hh
    dsimp [E]
    linarith
  have ha0 : 0 ≤ a := (correction_exponent_relative ht hD).1
  have ha : a+3*e ≤ E := by
    have hh := (correction_exponent_relative ht hD).2
    change a ≤ 16*Real.exp 1*e at hh
    dsimp [E, C]
    linarith
  have hca : 1-a ≤ c := by
    have hh := Real.add_one_le_exp (-a)
    exact (by simpa [c, correction, a, d, add_comm] using hh)
  have hzlow : d*(1-3*e) ≤ z := by
    have hh := optimizer_lower hΔ ht hb hD
    change d-3*(t:ℝ)*Real.log d ≤ z at hh
    dsimp [d] at hh
    dsimp [e, relativeError, d]
    convert hh using 1 <;> field_simp [(D_large_basic ht hD).2.1.ne'] <;> ring
  have hap : 0 ≤ 1-a := by linarith
  have hep : 0 ≤ 1-3*e := by linarith
  have hprod := mul_le_mul hca hzlow (mul_nonneg hd.le hep) hc.le
  have hprodextra : 0 ≤ d*a*(3*e) := by positivity
  have hcz : d*(1-E) ≤ c*z := by
    have hreplace := mul_le_mul_of_nonneg_left ha hd.le
    nlinarith
  have hhalf : d/2 ≤ c*z := by nlinarith
  have hupper : c*z ≤ d := by
    have hh := mul_nonneg hz.le (sub_nonneg.mpr hc1)
    nlinarith
  have hczpos : 0 < c*z := mul_pos hc hz
  have hfrac : 1 ≤ d/(c*z) := (le_div_iff₀ hczpos).mpr (by simpa using hupper)
  have hΔ0 : 0 < Δ := by linarith
  have hGam := gamma_optimizer_identity hΔ0 (fugacity_pos hb hd) hc
  have hEq : Gamma Δ (fugacity Δ t b) (correction Δ t b)*D Δ t b/Δ = d/(c*z) := by
    rw [hGam]
    change (Δ/(c*z))*d/Δ = d/(c*z)
    field_simp
  rw [hEq, abs_of_nonneg (sub_nonneg.mpr hfrac)]
  have hsub : d/(c*z)-1 = (d-c*z)/(c*z) := by field_simp <;> ring
  rw [hsub]
  apply (div_le_iff₀ hczpos).mpr
  change d-c*z ≤ (4*C*e)*(c*z)
  rw [show 4*C*e = 4*E by dsimp [E]; ring]
  have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 4*E by positivity)
  nlinarith [mul_nonneg hd.le hE]

lemma admissible_eventually_regime (Δ : ℕ → ℝ) (t : ℕ → ℕ) (b : ℕ → ℝ)
    (h : AdmissibleReal Δ t b) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ i in Filter.atTop, 8*Real.exp 1*t i ≤ D (Δ i) (t i) (b i) ∧
      relativeError (Δ i) (t i) (b i) ≤ c := by
  have hsmall := h.2.2.eventually (Iio_mem_nhds (lt_min hc (show 0 < 1/(8*Real.exp 1) by positivity)))
  have hlarge := h.2.1.eventually_ge_atTop (Real.exp 1)
  filter_upwards [hsmall, hlarge] with i hi hDi
  have ht : (1:ℝ) ≤ t i := by exact_mod_cast (h.1 i).2.1
  have hDpos : 0 < D (Δ i) (t i) (b i) := (Real.exp_pos 1).trans_le hDi
  have hlog : 1 ≤ Real.log (D (Δ i) (t i) (b i)) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hDi
    simpa only [Real.log_exp] using hh
  have hi1 : relativeError (Δ i) (t i) (b i) < 1/(8*Real.exp 1) := hi.trans_le (min_le_right _ _)
  have hi2 : relativeError (Δ i) (t i) (b i) ≤ c := (hi.trans_le (min_le_left _ _)).le
  refine ⟨?_,hi2⟩
  unfold relativeError at hi1
  have hh := (div_lt_iff₀ hDpos).mp hi1
  have hh' := mul_lt_mul_of_pos_left hh (show 0 < 8*Real.exp 1 by positivity)
  have hcancel : (8*Real.exp 1)*(1/(8*Real.exp 1)*D (Δ i) (t i) (b i)) = D (Δ i) (t i) (b i) := by field_simp
  rw [hcancel] at hh'
  have htmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8*Real.exp 1*(t i:ℝ) by positivity)
  nlinarith

lemma proposition6_asymptotic :
    ∃ A : ℝ, 0 < A ∧ ∀ (Δ : ℕ → ℝ) (t : ℕ → ℕ) (b : ℕ → ℝ), AdmissibleReal Δ t b →
      ∀ᶠ i in Filter.atTop,
        |Gamma (Δ i) (fugacity (Δ i) (t i) (b i)) (correction (Δ i) (t i) (b i)) *
          D (Δ i) (t i) (b i) / Δ i - 1| ≤ A * relativeError (Δ i) (t i) (b i) := by
  refine ⟨4*(16*Real.exp 1+3), by positivity, ?_⟩
  intro Δ t b h
  have hh := admissible_eventually_regime Δ t b h
    (c := 1/(4*(16*Real.exp 1+3))) (by positivity)
  filter_upwards [hh] with i hi
  exact quantitative_gamma_error (h.1 i).1 (h.1 i).2.1 (h.1 i).2.2 hi.1 hi.2

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma cThree_le_Gamma {Δ : ℕ} {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c) :
    0 < Gamma Δ lam c ∧ 0 ≤ cThree Δ lam c ∧ cThree Δ lam c ≤ (1+3*(Δ:ℝ))*Gamma Δ lam c := by
  let z := optimizer Δ lam c
  have hz : 0 ≤ z := (lambert_facts (div_nonneg (mul_nonneg (p_pos hlam).le (Nat.cast_nonneg Δ)) hc.le)).1
  have hβ : 0 < beta lam z := div_pos (Real.exp_pos _) (mul_pos (p_pos hlam) (by linarith))
  have hγ : 0 < gamma c z := one_div_pos.mpr (mul_pos hc (by linarith))
  have hp : p lam ≤ 1 := by unfold p; apply (div_le_one (by positivity)).mpr; linarith
  have hβΓ : beta lam z ≤ Gamma Δ lam c := by unfold Gamma; change _ ≤ beta lam z+gamma c z*Δ; linarith [mul_nonneg hγ.le (Nat.cast_nonneg Δ : (0:ℝ) ≤ _)]
  have hγΓ : gamma c z*Δ ≤ Gamma Δ lam c := by unfold Gamma; change _ ≤ beta lam z+gamma c z*Δ; linarith
  have hmax : max (beta lam z*p lam) (gamma c z*Δ) ≤ Gamma Δ lam c := by
    apply max_le
    · exact (mul_le_of_le_one_right hβ.le hp).trans hβΓ
    · exact hγΓ
  have hmax0 : 0 ≤ max (beta lam z*p lam) (gamma c z*Δ) :=
    (mul_nonneg hβ.le (p_pos hlam).le).trans (le_max_left _ _)
  refine ⟨by unfold Gamma; change 0 < beta lam z+gamma c z*Δ; positivity, ?_, ?_⟩
  · unfold cThree transferConstant
    change 0 ≤ beta lam z+_ *max (beta lam z*p lam) (gamma c z*Δ)
    positivity
  · unfold cThree transferConstant
    push_cast
    change beta lam z+3*(Δ:ℝ)*max (beta lam z*p lam) (gamma c z*Δ) ≤ _
    have hh := mul_le_mul_of_nonneg_left hmax (show 0 ≤ 3*(Δ:ℝ) by positivity)
    nlinarith

lemma nat_ceil_max_bound {x : ℝ} (hx : 0 ≤ x) : (max 1 ⌈x⌉₊ : ℕ) ≤ x+1 := by
  have hc := Nat.ceil_lt_add_one hx
  have h1 : (1:ℝ) ≤ x+1 := by linarith
  rw [Nat.cast_max,Nat.cast_one]
  exact max_le h1 hc.le

lemma entropy_parameter_bound (n : ℕ) {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    entropyBound n (fugacity Δ t b) ≤ 3*n*(Real.log (scale t b)+t*Real.log (D Δ t b)) := by
  let d := D Δ t b
  let lam := fugacity Δ t b
  have hd0 : 0 < d := (D_large_basic ht hD).2.1
  have hd1 : 1 ≤ d := (D_large_basic ht hD).2.2
  have hlam : 0 < lam := fugacity_pos hb hd0
  have hLam1 : lam ≤ 1 := (fugacity_le_inv_D ht hb hd1).trans ((div_le_one hd0).mpr hd1)
  have hlogd : 1 ≤ Real.log d := log_D_one_le ht hD
  have hlogs : 0 ≤ Real.log (scale t b) := Real.log_nonneg (scale_one_le ht hb)
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hr : ((2*t-1:ℕ):ℝ) = 2*(t:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ 2*t)]; norm_num
  have he : Real.log ((1+lam)/min 1 lam) = Real.log (1+lam)+Real.log (scale t b)+(2*(t:ℝ)-1)*Real.log d := by
    rw [min_eq_right hLam1,Real.log_div (by positivity) hlam.ne']
    dsimp [lam,fugacity]
    rw [one_div,Real.log_inv,Real.log_mul (scale_pos t hb).ne' (pow_pos hd0 _).ne',Real.log_pow,hr]
    ring
  have hloglam : Real.log (1+lam) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1+lam by positivity)
    linarith
  unfold entropyBound
  rw [he]
  have hh : Real.log (1+lam)+Real.log (scale t b)+(2*(t:ℝ)-1)*Real.log d ≤
      3*(Real.log (scale t b)+t*Real.log d) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n : (0:ℝ) ≤ _)
  nlinarith

lemma horizon_parameter_bound (n Δ : ℕ) {b : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ)
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hΓ : Gamma Δ (fugacity Δ t b) (correction Δ t b) ≤ 2*Δ/D Δ t b)
    {ε : ℝ} (hε : 0 < ε) :
    (horizon n Δ (fugacity Δ t b) (correction Δ t b) ε:ℝ) ≤
      400*(1+n*(Δ:ℝ)^4*(Real.log (scale t b)+t*Real.log (D Δ t b))/(ε^2*D Δ t b^2)) := by
  let lam := fugacity Δ t b
  let c := correction Δ t b
  let d := D Δ t b
  let L := Real.log (scale t b)+t*Real.log d
  have hd0 : 0 < d := (D_large_basic ht hD).2.1
  have hlam : 0 < lam := fugacity_pos hb hd0
  have hc : 0 < c := (correction_bounds ht hD).1
  have hC := cThree_le_Gamma (Δ := Δ) hlam hc
  have hΔ' : (1:ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hCl : cThree Δ lam c ≤ 8*(Δ:ℝ)^2/d := by
    have hh := mul_le_mul_of_nonneg_left hΓ (show 0 ≤ 1+3*(Δ:ℝ) by positivity)
    have hlin : 1+3*(Δ:ℝ) ≤ 4*Δ := by linarith
    have hm := mul_le_mul_of_nonneg_right hlin (show 0 ≤ 2*(Δ:ℝ)/d by positivity)
    calc
      _ ≤ (1+3*(Δ:ℝ))*(2*Δ/d) := hC.2.2.trans hh
      _ ≤ 4*(Δ:ℝ)*(2*Δ/d) := hm
      _ = _ := by ring
  have hCsq := pow_le_pow_left₀ hC.2.1 hCl 2
  have hH := entropy_parameter_bound n ht hb hD
  have hL : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg (Real.log_nonneg (scale_one_le ht hb)) (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (D_large_basic ht hD).2.2))
  have hH0 : 0 ≤ entropyBound n lam := by
    unfold entropyBound
    have hr : 1 ≤ (1+lam)/min 1 lam := by
      apply (le_div_iff₀ (lt_min (by norm_num) hlam)).mpr
      have hh := min_le_left (1:ℝ) lam
      linarith
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hr)
  have hX : 0 ≤ 2*cThree Δ lam c^2*entropyBound n lam/ε^2 := by positivity
  have hceil := nat_ceil_max_bound hX
  change ((max 1 ⌈2*cThree Δ lam c^2*entropyBound n lam/ε^2⌉₊:ℕ):ℝ) ≤ _
  have hprod := mul_le_mul hCsq hH hH0 (sq_nonneg (8*(Δ:ℝ)^2/d))
  have hbound : 2*cThree Δ lam c^2*entropyBound n lam/ε^2 ≤
      384*n*(Δ:ℝ)^4*L/(ε^2*d^2) := by
    apply (div_le_iff₀ (sq_pos_of_pos hε)).mpr
    have hden : d^2 ≠ 0 := (sq_pos_of_pos hd0).ne'
    apply (le_of_mul_le_mul_right (a := d^2) _ (sq_pos_of_pos hd0))
    field_simp at hprod ⊢
    nlinarith
  have hbase : 0 ≤ n*(Δ:ℝ)^4*L/(ε^2*d^2) := by positivity
  dsimp only [lam,c,d,L] at hceil hbound hbase ⊢
  ring_nf at hceil hbound hbase ⊢
  linarith

end
end LocalOccupancyIS.Glauber

set_option maxHeartbeats 1000000
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma charges_polynomial (n Δ T R : ℕ) :
    ((executionCharges n Δ T R).total:ℝ) ≤
      20*(n+1)^2*((Δ:ℝ)+1)*(T+1)*(R+1) := by
  unfold executionCharges Charges.total
  push_cast
  apply le_of_sub_nonneg
  ring_nf
  positivity

lemma log_scale_add_D {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (hb : 0 ≤ b) :
    Real.log (scale t b)+D Δ t b = Real.log Δ := by
  unfold D rho
  rw [Real.log_div hΔ.ne' (scale_pos t hb).ne']
  ring

lemma algorithm_cost_polynomial (n Δ t : ℕ) {b : ℝ} (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hrel : relativeError Δ t b ≤ 1)
    (hΓ : Gamma Δ (fugacity Δ t b) (correction Δ t b) ≤ 2*Δ/D Δ t b)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (algorithmCost n Δ t b (1/D Δ t b) δ:ℝ) ≤ 1000000*(n+1)^10*(1+Real.log (1/δ))^10 := by
  let d := D Δ t b
  let lam := fugacity Δ t b
  let c := correction Δ t b
  let N : ℝ := n+1
  let L := 1+Real.log (1/δ)
  let T := horizon n Δ lam c (1/d)
  let R := repeats Δ lam c (1/d) δ
  have hN : 1 ≤ N := by dsimp only [N]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ _)]
  have hΔ' : (1:ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hΔn' : (Δ:ℝ) ≤ n := by exact_mod_cast hΔn
  have hd0 : 0 < d := (D_large_basic ht hD).2.1
  have hlog : 0 ≤ Real.log (1/δ) := by apply Real.log_nonneg; apply (one_le_div hδ).mpr; exact hδ1.le
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hr : (t:ℝ)*Real.log d ≤ d := by
    have hh := (div_le_iff₀ hd0).mp hrel
    simpa [relativeError,d] using hh
  have hlogs : Real.log (scale t b)+t*Real.log d ≤ (Δ:ℝ) := by
    have hh := add_le_add (le_refl (Real.log (scale t b))) hr
    rw [log_scale_add_D (by linarith : (0:ℝ) < Δ) hb] at hh
    have hl := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < Δ)
    exact hh.trans (by linarith)
  have hL0 : 0 ≤ Real.log (scale t b)+t*Real.log d :=
    add_nonneg (Real.log_nonneg (scale_one_le ht hb))
      (mul_nonneg (Nat.cast_nonneg t) (Real.log_nonneg (D_large_basic ht hD).2.2))
  have hT0 := horizon_parameter_bound n Δ hΔ ht hb hD hΓ (one_div_pos.mpr hd0)
  have hT1 : (T:ℝ) ≤ 400*(1+n*(Δ:ℝ)^4*(Real.log (scale t b)+t*Real.log d)) := by
    have heq : (1/d)^2*d^2 = 1 := by field_simp
    change (T:ℝ) ≤ 400*(1+n*(Δ:ℝ)^4*(Real.log (scale t b)+t*Real.log d)/((1/d)^2*d^2)) at hT0
    simpa only [heq,div_one] using hT0
  have hT : (T:ℝ)+1 ≤ 801*N^6 := by
    have hp : n*(Δ:ℝ)^4*(Real.log (scale t b)+t*Real.log d) ≤ N^6 := by
      calc
        _ ≤ N*N^4*N := by gcongr <;> (try dsimp only [N]) <;> linarith
        _ = _ := by ring
    have hN6 : 1 ≤ N^6 := one_le_pow₀ hN
    nlinarith
  have hΓ0 := (cThree_le_Gamma (Δ := Δ) (fugacity_pos hb hd0) (correction_bounds ht hD).1).1
  have hR0 : (R:ℝ) ≤ (2*Gamma Δ lam c/(1/d))*Real.log (1/δ)+1 := by
    exact nat_ceil_max_bound (by positivity)
  have hR : (R:ℝ)+1 ≤ 6*N*L := by
    have hh' : Gamma Δ lam c*d ≤ 2*Δ := by
      exact (le_div_iff₀ hd0).mp hΓ
    have hmul := mul_le_mul_of_nonneg_right hh' hlog
    have heq : (2*Gamma Δ lam c/(1/d))*Real.log (1/δ) = 2*(Gamma Δ lam c*d)*Real.log (1/δ) := by field_simp <;> ring
    rw [heq] at hR0
    dsimp only [N,L] at hR0 hmul ⊢
    nlinarith
  have hc0 := charges_polynomial n Δ T R
  have hbound : 20*(n+1)^2*((Δ:ℝ)+1)*(T+1)*(R+1) ≤ 1000000*N^10*L^10 := by
    have hΔN : (Δ:ℝ)+1 ≤ N := by dsimp [N]; linarith
    calc
      _ ≤ 20*N^2*N*(801*N^6)*(6*N*L) := by gcongr
      _ = 96120*N^10*L := by ring
      _ ≤ 1000000*N^10*L^10 := by
        have hLp : L ≤ L^10 := le_self_pow₀ hL (by norm_num)
        have hh := mul_le_mul_of_nonneg_left hLp (show 0 ≤ 96120*N^10 by positivity)
        have hnn : 0 ≤ N^10*L^10 := by positivity
        nlinarith
  exact hc0.trans hbound

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma success_threshold_mono {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) {a b : ℝ} (hab : a ≤ b) : success G ν b ≤ success G ν a := by
  apply Finset.sum_le_sum
  intro I _
  by_cases hb : b ≤ (size I.val:ℝ)
  · simp [hb,hab.trans hb]
  · simp only [hb,if_false]
    split_ifs
    · exact hν.1 I
    · rfl

lemma headline_size_bound {N d Δ Γ a ε : ℝ} (hN : 0 ≤ N) (hd : 0 < d)
    (hΔ : 0 < Δ) (hΓ : 0 < Γ) (ha : 0 ≤ a) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hupper : Γ*d/Δ ≤ 1+a) :
    (1-a-ε)*N*d/Δ ≤ (1-ε)*N/Γ := by
  by_cases hf : 0 ≤ 1-a-ε
  · apply (le_div_iff₀ hΓ).mpr
    calc
      _ = N*(1-a-ε)*(Γ*d/Δ) := by ring
      _ ≤ N*(1-a-ε)*(1+a) := mul_le_mul_of_nonneg_left hupper (mul_nonneg hN hf)
      _ ≤ _ := by nlinarith [mul_nonneg hN (sq_nonneg a),mul_nonneg hN (mul_nonneg ha hε)]
  · have hl : (1-a-ε)*N*d/Δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hf) hN) hd.le) hΔ.le
    exact hl.trans (div_nonneg (mul_nonneg (by linarith) hN) hΓ.le)

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section


lemma exact_regime {n Δ t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) {b : ℝ} (hb : 0 ≤ b) (hmax : MaximumDegree G Δ)
    (hd : HereditaryDensity G t b) (hD : 1000*Real.exp 1*t ≤ D Δ t b)
    (hsmall : relativeError Δ t b ≤ 1/(4*(16*Real.exp 1+3)))
    (w : Fin n → List (Fin n)) (hw : ∀ u, IsSweep (G.neighborFinset u) (w u)) :
    ExactConclusion G Δ t b w ((4*(16*Real.exp 1+3)+2)*t) 1000000 10 := by
  let C := 4*(16*Real.exp 1+3)
  let d := D Δ t b
  let lam := fugacity Δ t b
  let c := correction Δ t b
  let e := relativeError Δ t b
  have hDsmall : 8*Real.exp 1*t ≤ d := by dsimp [d]; nlinarith [Real.exp_pos 1]
  have hd0 : 0 < d := (D_large_basic ht hDsmall).2.1
  have hd8 : 8 ≤ d := (D_large_basic ht hDsmall).1
  have hΔ' : (1:ℝ) ≤ Δ := by exact_mod_cast hΔ
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hlog : 1 ≤ Real.log d := log_D_one_le ht hDsmall
  have hC : 1 ≤ C := by dsimp [C]; have he := Real.exp_pos 1; linarith
  have he : 0 ≤ e := by dsimp [e,relativeError]; positivity
  have hCe : C*e ≤ 1 := by simpa only [mul_comm] using (le_div_iff₀ (by linarith : 0 < C)).mp hsmall
  have he1 : e ≤ 1 := by nlinarith
  have herr := quantitative_gamma_error hΔ' ht hb hDsmall hsmall
  change |Gamma Δ lam c*d/Δ-1| ≤ C*e at herr
  have hΓupper : Gamma Δ lam c*d/Δ ≤ 1+C*e := by have hh := (abs_le.mp herr).2; linarith
  have hΓ : Gamma Δ lam c ≤ 2*Δ/d := by
    apply (le_div_iff₀ hd0).mpr
    have hh := (div_le_iff₀ (by linarith : (0:ℝ) < Δ)).mp hΓupper
    nlinarith
  have hlam : 0 < lam := fugacity_pos hb hd0
  have hc : 0 < c := (correction_bounds ht hDsmall).1
  have hΓ0 : 0 < Gamma Δ lam c := (cThree_le_Gamma (Δ := Δ) hlam hc).1
  obtain ⟨v,hv⟩ := hmax.2
  letI : Nonempty (Fin n) := ⟨v⟩
  have hΔn : Δ ≤ n := by have hh := SimpleGraph.degree_lt_card_verts (G := G) v; simp only [Fintype.card_fin,hv] at hh; omega
  have hf := three_sweep_finite G Δ t b hΔ hmax.1 ht hb hd hD w hw
  have herror : |Gamma Δ lam c*d/Δ-1| ≤ ((C+2)*t)*Real.log d/d := by
    calc
      _ ≤ C*e := herr
      _ ≤ ((C+2)*t)*Real.log d/d := by
        have heq : ((C+2)*t)*Real.log d/d = (C+2)*e := by change _ = (C+2)*((t:ℝ)*Real.log d/d); ring
        rw [heq]
        nlinarith
  refine ⟨hf,herror,?_,?_,?_⟩
  · intro I δ hδ hδ1
    have hε : 0 < 1/d := by positivity
    have hε1 : 1/d < 1 := (div_lt_one hd0).mpr (by linarith)
    have hfin := hf.2.2.2.2.2.2 I (1/d) δ hε hε1 hδ hδ1
    dsimp only at hfin
    have hdist : MarkovMixing.IsDist (algorithm G Δ t b (1/d) δ I) := hfin.1
    have hthreshold : (1-((C+2)*t)*Real.log d/d)*n*d/Δ ≤ (1-1/d)*n/Gamma Δ lam c := by
      have hbase := headline_size_bound (N := n) (Nat.cast_nonneg _) hd0 (by linarith : (0:ℝ) < Δ)
        hΓ0 (mul_nonneg (by linarith : 0 ≤ C) he) hε.le hε1.le hΓupper
      have heps : 1/d ≤ 2*e := by
        have hh : 1 ≤ 2*((t:ℝ)*Real.log d) := by nlinarith
        have hm := div_le_div_of_nonneg_right hh hd0.le
        change 1/d ≤ 2*((t:ℝ)*Real.log d/d)
        simpa only [mul_div_assoc] using hm
      have hfac : 1-((C+2)*t)*Real.log d/d ≤ 1-C*e-1/d := by
        have heq : ((C+2)*t)*Real.log d/d = (C+2)*e := by change _ = (C+2)*((t:ℝ)*Real.log d/d); ring
        rw [heq]
        nlinarith
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg n)) hd0.le) (Nat.cast_nonneg Δ)).trans hbase
    have hsfin : 1-δ ≤ success G (algorithm G Δ t b (1/d) δ I) ((1-1/d)*n/Gamma Δ lam c) := by
      simpa only [algorithm,Fintype.card_fin] using hfin.2.2
    have hs := hsfin.trans (success_threshold_mono G hdist hthreshold)
    have hcost := algorithm_cost_polynomial n Δ t hΔ hΔn ht hb hDsmall he1 hΓ hδ hδ1
    exact ⟨hdist,hs,hcost⟩
  · intro ε hε _
    have hh := horizon_parameter_bound n Δ hΔ ht hb hDsmall hΓ hε
    have hL : 0 ≤ 1+n*(Δ:ℝ)^4*(Real.log (scale t b)+t*Real.log d)/(ε^2*d^2) := by
      have hs := Real.log_nonneg (scale_one_le ht hb)
      positivity
    nlinarith
  · intro I J u
    exact ⟨spin_hardcore G I u false,spin_hardcore G I u true,single_site_formula G hlam I J u⟩

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma fixed_regime_threshold (t : ℕ) (ht : 1 ≤ t) :
    ∃ R : ℝ, 1 < R ∧ ∀ (Δ b : ℝ), 0 ≤ b → R ≤ rho Δ t b →
      1000*Real.exp 1*t ≤ D Δ t b ∧ relativeError Δ t b ≤ 1/(4*(16*Real.exp 1+3)) := by
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul (t:ℝ)
  simp only [mul_zero] at hlim
  have hsmall := hlim.eventually (Iio_mem_nhds (show (0:ℝ) < 1/(4*(16*Real.exp 1+3)) by positivity))
  obtain ⟨d₀,hd₀⟩ := Filter.eventually_atTop.mp hsmall
  let d₁ := max d₀ (1000*Real.exp 1*t)
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hd₁ : 0 < d₁ := lt_of_lt_of_le (by positivity : 0 < 1000*Real.exp 1*(t:ℝ)) (le_max_right _ _)
  refine ⟨Real.exp d₁, ?_, ?_⟩
  · simpa using Real.exp_lt_exp.mpr hd₁
  · intro Δ b hb hr
    have hd : d₁ ≤ D Δ t b := by
      have hh := Real.log_le_log (Real.exp_pos d₁) hr
      simpa only [Real.log_exp,D] using hh
    refine ⟨(le_max_right _ _).trans hd, ?_⟩
    have hh := (hd₀ (D Δ t b) ((le_max_left _ _).trans hd)).le
    simpa only [relativeError,mul_div_assoc,id_eq] using hh

lemma growing_regime (Δ t : ℕ → ℕ) (b : ℕ → ℝ) (h : Admissible Δ t b) :
    ∀ᶠ i in Filter.atTop, 1000*Real.exp 1*t i ≤ D (Δ i) (t i) (b i) ∧
      relativeError (Δ i) (t i) (b i) ≤ 1/(4*(16*Real.exp 1+3)) := by
  have hsmall := h.2.2.eventually (Iio_mem_nhds (lt_min
    (show (0:ℝ) < 1/(4*(16*Real.exp 1+3)) by positivity)
    (show (0:ℝ) < 1/(1000*Real.exp 1) by positivity)))
  have hlarge := h.2.1.eventually_ge_atTop (Real.exp 1)
  filter_upwards [hsmall,hlarge] with i hi hDi
  have ht : (1:ℝ) ≤ t i := by exact_mod_cast (h.1 i).2.1
  have hd : 0 < D (Δ i) (t i) (b i) := (Real.exp_pos 1).trans_le hDi
  have hlog : 1 ≤ Real.log (D (Δ i) (t i) (b i)) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hDi
    simpa only [Real.log_exp] using hh
  have hi1 := hi.trans_le (min_le_right _ _)
  have hi2 := (hi.trans_le (min_le_left _ _)).le
  refine ⟨?_,hi2⟩
  unfold relativeError at hi1
  have hh := (div_lt_iff₀ hd).mp hi1
  have hm := mul_lt_mul_of_pos_left hh (show 0 < 1000*Real.exp 1 by positivity)
  have heq : (1000*Real.exp 1)*(1/(1000*Real.exp 1)*D (Δ i) (t i) (b i)) = D (Δ i) (t i) (b i) := by field_simp
  rw [heq] at hm
  have htlog := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1000*Real.exp 1*(t i:ℝ) by positivity)
  nlinarith

lemma exact_fixed (t : ℕ) (ht : 1 ≤ t) :
    ∃ Aₜ Rₜ Bₜ : ℝ, 0 < Aₜ ∧ 1 < Rₜ ∧ 0 < Bₜ ∧
      ∀ n Δ : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
      ∀ b : ℝ, 1 ≤ Δ → 0 ≤ b → MaximumDegree G Δ → HereditaryDensity G t b →
      Rₜ ≤ rho Δ t b → ∀ w : Fin n → List (Fin n),
      (∀ u, IsSweep (G.neighborFinset u) (w u)) → ExactConclusion G Δ t b w Aₜ Bₜ 10 := by
  obtain ⟨R,hR,hreg⟩ := fixed_regime_threshold t ht
  refine ⟨(4*(16*Real.exp 1+3)+2)*t,R,1000000,by positivity,hR,by norm_num,?_⟩
  intro n Δ G inst b hΔ hb hmax hd hr w hw
  have hh := hreg Δ b hb hr
  exact exact_regime G hΔ ht hb hmax hd hh.1 hh.2 w hw

lemma exact_growing (Δ t : ℕ → ℕ) (b : ℕ → ℝ) (h : Admissible Δ t b) :
    ∀ᶠ i in Filter.atTop, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
      MaximumDegree G (Δ i) → HereditaryDensity G (t i) (b i) →
        ∀ w : Fin n → List (Fin n), (∀ u, IsSweep (G.neighborFinset u) (w u)) →
          ExactConclusion G (Δ i) (t i) (b i) w ((4*(16*Real.exp 1+3)+2)*t i) 1000000 10 := by
  filter_upwards [growing_regime Δ t b h] with i hi
  intro n G inst hmax hd w hw
  exact exact_regime G (h.1 i).1 (h.1 i).2.1 (h.1 i).2.2 hmax hd hi.1 hi.2 w hw

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma D_log_formula {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (hb : 0 ≤ b) :
    D Δ t b = Real.log Δ-Real.log (b+1)/(2*(t:ℝ)-1) := by
  unfold D rho scale
  rw [Real.log_div hΔ.ne' (Real.rpow_pos_of_pos (by linarith : 0 < b+1) _).ne',Real.log_rpow (by linarith : 0 < b+1)]
  ring

lemma subpoly_limits (t : ℕ) (ht : 1 ≤ t) (Δ : ℕ → ℕ) (b : ℕ → ℝ)
    (hb : ∀ i, 1 ≤ Δ i ∧ 0 ≤ b i) (hΔ : Filter.Tendsto Δ Filter.atTop Filter.atTop)
    (hsub : Filter.Tendsto (fun i => Real.log (b i+1)/Real.log (Δ i)) Filter.atTop (nhds 0)) :
    Admissible Δ (fun _ => t) b ∧
    Filter.Tendsto (fun i => D (Δ i) t (b i)/Real.log (Δ i)) Filter.atTop (nhds 1) := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hden : 0 < 2*(t:ℝ)-1 := by linarith
  have hreal : Filter.Tendsto (fun i => (Δ i:ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hΔ
  have hlog := Real.tendsto_log_atTop.comp hreal
  have hlogpos := hlog.eventually_ge_atTop 1
  have hcoef : Filter.Tendsto (fun i => 1-(Real.log (b i+1)/Real.log (Δ i))/(2*(t:ℝ)-1))
      Filter.atTop (nhds 1) := by
    have hh := (tendsto_const_nhds (x := (1:ℝ))).sub (hsub.div_const (2*(t:ℝ)-1))
    simpa using hh
  have hproduct := Filter.Tendsto.atTop_mul_pos (by norm_num : (0:ℝ) < 1) hlog hcoef
  have heq : ∀ᶠ i in Filter.atTop,
      Real.log (Δ i)*(1-(Real.log (b i+1)/Real.log (Δ i))/(2*(t:ℝ)-1)) = D (Δ i) t (b i) := by
    filter_upwards [hlogpos] with i hi
    change 1 ≤ Real.log (Δ i) at hi
    rw [D_log_formula (by exact_mod_cast (show 0 < Δ i by have hh := (hb i).1; omega)) (hb i).2]
    have hL : Real.log (Δ i) ≠ 0 := by linarith
    field_simp
    <;> ring
  have hD : Filter.Tendsto (fun i => D (Δ i) t (b i)) Filter.atTop Filter.atTop := hproduct.congr' heq
  have hratio : Filter.Tendsto (fun i => D (Δ i) t (b i)/Real.log (Δ i)) Filter.atTop (nhds 1) := by
    apply hcoef.congr'
    filter_upwards [hlogpos,heq] with i hi he
    change 1 ≤ Real.log (Δ i) at hi
    rw [← he]
    field_simp [show Real.log (Δ i) ≠ 0 by linarith]
  have herr0 := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hD).const_mul (t:ℝ)
  have herr : Filter.Tendsto (fun i => relativeError (Δ i) t (b i)) Filter.atTop (nhds 0) := by
    simpa only [relativeError,id_eq,Function.comp_apply,mul_zero,mul_div_assoc] using herr0
  exact ⟨⟨fun i => ⟨(hb i).1,ht,(hb i).2⟩,hD,herr⟩,hratio⟩

lemma subpoly_leading (t : ℕ) (ht : 1 ≤ t) (Δ : ℕ → ℕ) (b : ℕ → ℝ)
    (hb : ∀ i, 1 ≤ Δ i ∧ 0 ≤ b i) (hΔ : Filter.Tendsto Δ Filter.atTop Filter.atTop)
    (hsub : Filter.Tendsto (fun i => Real.log (b i+1)/Real.log (Δ i)) Filter.atTop (nhds 0)) :
    ∃ Bₜ : ℝ, 0 < Bₜ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in Filter.atTop,
      ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
        MaximumDegree G (Δ i) → HereditaryDensity G t (b i) →
          LeadingOne G (Δ i) t (b i) ζ Bₜ 10 := by
  let A : ℝ := (4*(16*Real.exp 1+3)+2)*t
  have hlim := subpoly_limits t ht Δ b hb hΔ hsub
  have hD := hlim.1.2.1
  have herr := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hD
  have hnormalized : Filter.Tendsto
      (fun i => D (Δ i) t (b i)/Real.log (Δ i)-A*((Real.log (D (Δ i) t (b i))/D (Δ i) t (b i))*(D (Δ i) t (b i)/Real.log (Δ i))))
      Filter.atTop (nhds 1) := by
    have hh := hlim.2.sub ((herr.mul hlim.2).const_mul A)
    simpa only [id_eq,Function.comp_apply,zero_mul,mul_zero,sub_zero] using hh
  refine ⟨1000000,by norm_num,?_⟩
  intro ζ hζ
  have hhead := hnormalized.eventually (Ioi_mem_nhds (show 1-ζ < 1 by linarith))
  have hlarge := hD.eventually_ge_atTop 1
  have hloglarge := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hΔ)).eventually_ge_atTop 1
  filter_upwards [exact_growing Δ (fun _ => t) b hlim.1,hhead,hlarge,hloglarge] with i hex hhi hdi hli
  change 1 ≤ Real.log (Δ i) at hli
  intro n G inst hmax hd I δ hδ hδ1
  let w : Fin n → List (Fin n) := fun u => (G.neighborFinset u).toList
  have hw : ∀ u, IsSweep (G.neighborFinset u) (w u) := fun u => ⟨Finset.nodup_toList _,by simp [w]⟩
  have hcon := hex n G inst hmax hd w hw
  have hout := hcon.2.2.1 I δ hδ hδ1
  have hΓ : 0 < (Δ i:ℝ) := by exact_mod_cast (show 0 < Δ i by have hh := (hb i).1; omega)
  have hd0 : 0 < D (Δ i) t (b i) := by linarith
  have hl0 : 0 < Real.log (Δ i) := by linarith
  have hthreshold : (1-ζ)*n*Real.log (Δ i)/Δ i ≤
      (1-A*Real.log (D (Δ i) t (b i))/D (Δ i) t (b i))*n*D (Δ i) t (b i)/Δ i := by
    have hh := mul_le_mul_of_nonneg_right hhi.le (show 0 ≤ Real.log (Δ i) by linarith)
    have heq : (D (Δ i) t (b i)/Real.log (Δ i)-A*((Real.log (D (Δ i) t (b i))/D (Δ i) t (b i))*(D (Δ i) t (b i)/Real.log (Δ i))))*Real.log (Δ i) =
        D (Δ i) t (b i)-A*Real.log (D (Δ i) t (b i)) := by field_simp <;> ring
    rw [heq] at hh
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg n : (0:ℝ) ≤ _)) hΓ.le
    convert hm using 1 <;> first | rfl | (field_simp <;> ring)
  exact ⟨hout.2.1.trans (success_threshold_mono G hout.1 hthreshold),hout.2.2⟩

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

def mapParts {V W : Type} [DecidableEq V] [DecidableEq W] (f : V ↪ W) : Finset V ↪ Finset W :=
  ⟨Finset.map f,Finset.map_injective f⟩

lemma bicliques_map {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (G : SimpleGraph W) [DecidableRel F.Adj] [DecidableRel G.Adj]
    (f : V ↪ W) (hf : ∀ v z, F.Adj v z → G.Adj (f v) (f z)) (t : ℕ)
    {C : Finset (Finset V)} (hC : C ∈ bicliques F t) : C.map (mapParts f) ∈ bicliques G t := by
  classical
  simp only [bicliques,Finset.mem_filter,Finset.mem_powerset] at hC ⊢
  refine ⟨?_,by simpa using hC.2.1,?_⟩
  · intro A hA
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hA
    have hh := hC.1 ha
    simp only [Finset.mem_filter,Finset.mem_powerset] at hh ⊢
    exact ⟨Finset.subset_univ _,by simpa [mapParts] using hh.2⟩
  · intro A hA B hB hAB
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hA
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hB
    have hab : a ≠ b := by intro he; exact hAB (congrArg (mapParts f) he)
    have hh := hC.2.2 a ha b hb hab
    constructor
    · apply Finset.disjoint_left.mpr
      intro z hza hzb
      obtain ⟨v,hv,hfv⟩ := Finset.mem_map.mp hza
      obtain ⟨w,hw,hfw⟩ := Finset.mem_map.mp hzb
      have hvw : v = w := f.injective (hfv.trans hfw.symm)
      exact Finset.disjoint_left.mp hh.1 hv (hvw.symm ▸ hw)
    · intro v hv z hz
      obtain ⟨a',ha',rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨b',hb',rfl⟩ := Finset.mem_map.mp hz
      exact hf a' b' (hh.2 a' ha' b' hb')

lemma apex_hereditary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (t : ℕ) (h : ApexFree G t) : HereditaryDensity G t 0 := by
  classical
  intro u A hA
  have hempty : bicliques (G.induce (↑A : Set (Fin n))) t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro C hC
    let f : (↑(↑A : Set (Fin n))) ↪ ↑(↑(G.neighborFinset u) : Set (Fin n)) :=
      ⟨fun v => ⟨v.val,hA v.property⟩,fun v z he => Subtype.ext (congrArg (fun x => x.val) he)⟩
    have hh := bicliques_map (G.induce (↑A : Set (Fin n)))
      (G.induce (↑(G.neighborFinset u) : Set (Fin n))) f (by intro v z hvz; exact hvz) t hC
    rw [h u] at hh
    simpa using hh
  simp [Density,hempty]

lemma apex_admissible (Δ t : ℕ → ℕ) (hpos : ∀ i, 1 ≤ Δ i ∧ 1 ≤ t i)
    (hΔ : Filter.Tendsto Δ Filter.atTop Filter.atTop)
    (he : Filter.Tendsto (fun i => (t i:ℝ)*Real.log (Real.log (Δ i))/Real.log (Δ i)) Filter.atTop (nhds 0)) :
    Admissible Δ t (fun _ => 0) := by
  have hD (i : ℕ) : D (Δ i) (t i) 0 = Real.log (Δ i) := by simp [D,rho,scale]
  refine ⟨fun i => ⟨(hpos i).1,(hpos i).2,by rfl⟩,?_,?_⟩
  · simpa only [hD,Function.comp_def] using Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hΔ)
  · simpa only [relativeError,hD] using he

lemma apex_leading (Δ t : ℕ → ℕ) (hpos : ∀ i, 1 ≤ Δ i ∧ 1 ≤ t i)
    (hΔ : Filter.Tendsto Δ Filter.atTop Filter.atTop)
    (he : Filter.Tendsto (fun i => (t i:ℝ)*Real.log (Real.log (Δ i))/Real.log (Δ i)) Filter.atTop (nhds 0))
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∀ᶠ i in Filter.atTop, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
      MaximumDegree G (Δ i) → ApexFree G (t i) → LeadingOne G (Δ i) (t i) 0 ζ 1000000 10 := by
  let C := 4*(16*Real.exp 1+3)+2
  have hC : 0 < C := by dsimp [C]; positivity
  have hh := he.const_mul C
  simp only [mul_zero] at hh
  have hsmall := hh.eventually (Iio_mem_nhds hζ)
  have hadm := apex_admissible Δ t hpos hΔ he
  have hD (i : ℕ) : D (Δ i) (t i) 0 = Real.log (Δ i) := by simp [D,rho,scale]
  have hlarge := hadm.2.1.eventually_ge_atTop 1
  filter_upwards [exact_growing Δ t (fun _ => 0) hadm,hsmall,hlarge] with i hi herr hd
  intro n G inst hmax hfree I δ hδ hδ1
  let w : Fin n → List (Fin n) := fun u => (G.neighborFinset u).toList
  have hw : ∀ u, IsSweep (G.neighborFinset u) (w u) := fun u => ⟨Finset.nodup_toList _,by simp [w]⟩
  have hcon := hi n G inst hmax (apex_hereditary G (t i) hfree) w hw
  have hout := hcon.2.2.1 I δ hδ hδ1
  have hlog : 0 ≤ Real.log (Δ i) := by rw [hD] at hd; linarith
  have hΔ0 : 0 ≤ (Δ i:ℝ) := Nat.cast_nonneg _
  have hfac : 1-ζ ≤ 1-C*(t i:ℝ)*Real.log (Real.log (Δ i))/Real.log (Δ i) := by
    have heq : C*((t i:ℝ)*Real.log (Real.log (Δ i))/Real.log (Δ i)) = C*(t i:ℝ)*Real.log (Real.log (Δ i))/Real.log (Δ i) := by ring
    rw [heq] at herr
    linarith
  have hthreshold := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg n : (0:ℝ) ≤ _)) hlog) hΔ0
  simp only [hD] at hout
  simpa only [hD] using And.intro (hout.2.1.trans (success_threshold_mono G hout.1 hthreshold)) hout.2.2

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma cost_monomial_mono {n : ℕ} {δ B B' : ℝ} {k k' : ℕ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hB : 0 ≤ B) (hBB : B ≤ B') (hk : k ≤ k') :
    B*(n+1)^k*(1+Real.log (1/δ))^k ≤ B'*(n+1)^k'*(1+Real.log (1/δ))^k' := by
  have hn : (1:ℝ) ≤ n+1 := by have h := Nat.cast_nonneg n (α := ℝ); linarith
  have hlog : 0 ≤ Real.log (1/δ) := Real.log_nonneg ((one_le_div hδ).mpr hδ1.le)
  have hl : 1 ≤ 1+Real.log (1/δ) := by linarith
  have hnPow := pow_le_pow_right₀ hn hk
  have hlPow := pow_le_pow_right₀ hl hk
  have hB' : 0 ≤ B' := hB.trans hBB
  gcongr <;> positivity

lemma leading_weaken {n Δ t k k' : ℕ} {b ζ B B' : ℝ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hB : 0 ≤ B) (hBB : B ≤ B') (hk : k ≤ k')
    (h : LeadingOne G Δ t b ζ B k) : LeadingOne G Δ t b ζ B' k' := by
  intro I δ hδ hδ1
  have hh := h I δ hδ hδ1
  exact ⟨hh.1,hh.2.trans (cost_monomial_mono hδ hδ1 hB hBB hk)⟩

lemma exact_weaken {n Δ t k k' : ℕ} {b A B B' : ℝ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hB : 0 ≤ B) (hBB : B ≤ B') (hk : k ≤ k') (w : Fin n → List (Fin n))
    (h : ExactConclusion G Δ t b w A B k) : ExactConclusion G Δ t b w A B' k' := by
  refine ⟨h.1,h.2.1,?_,?_,h.2.2.2.2⟩
  · intro I δ hδ hδ1
    have hh := h.2.2.1 I δ hδ hδ1
    exact ⟨hh.1,hh.2.1,hh.2.2.trans (cost_monomial_mono hδ hδ1 hB hBB hk)⟩
  · intro ε hε hε1
    have hh := h.2.2.2.1 ε hε hε1
    have hnonneg : 0 ≤ 1+n*(Δ:ℝ)^4*(Real.log (scale t b)+t*Real.log (D Δ t b))/(ε^2*D Δ t b^2) := by
      have hs := Real.log_nonneg (scale_one_le ht hb)
      have hd := Real.log_nonneg (D_large_basic ht hD).2.2
      positivity
    exact hh.trans (mul_le_mul_of_nonneg_right hBB hnonneg)

end
end LocalOccupancyIS.Glauber

open LocalOccupancyIS.Glauber

/-- All of Corollary 4 and Remark 1, p.6; implementations pp.19–20.
Absolute constants/exponent precede all varying input sequences. -/
theorem solution :
    ∃ A B : ℝ, ∃ k : ℕ, 0 < A ∧ 0 < B ∧ 1 ≤ k ∧
    -- Fixed t: the threshold and constants precede b, graph, order and initial state.
    (∀ t : ℕ, 1 ≤ t → ∃ Aₜ Rₜ Bₜ : ℝ, 0 < Aₜ ∧ 1 < Rₜ ∧ 0 < Bₜ ∧
      ∀ n Δ : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
      ∀ b : ℝ, 1 ≤ Δ → 0 ≤ b → MaximumDegree G Δ → HereditaryDensity G t b →
      Rₜ ≤ rho Δ t b → ∀ w : Fin n → List (Fin n),
      (∀ u, IsSweep (G.neighborFinset u) (w u)) → ExactConclusion G Δ t b w Aₜ Bₜ k) ∧
    -- Growing t and b: one absolute error constant and one exponent.
    (∀ (Δ t : ℕ → ℕ) (b : ℕ → ℝ), Admissible Δ t b →
      ∀ᶠ i in Filter.atTop, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
        MaximumDegree G (Δ i) → HereditaryDensity G (t i) (b i) →
        ∀ w : Fin n → List (Fin n), (∀ u, IsSweep (G.neighborFinset u) (w u)) →
          ExactConclusion G (Δ i) (t i) (b i) w (A*t i) B k) ∧
    -- Fixed-t subpolynomial b+1 consequence, with the same actual algorithm.
    (∀ t : ℕ, 1 ≤ t → ∀ (Δ : ℕ → ℕ) (b : ℕ → ℝ),
      (∀ i, 1 ≤ Δ i ∧ 0 ≤ b i) → Filter.Tendsto Δ Filter.atTop Filter.atTop →
      Filter.Tendsto (fun i => Real.log (b i+1)/Real.log (Δ i)) Filter.atTop (nhds 0) →
      ∃ Bₜ : ℝ, 0 < Bₜ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in Filter.atTop,
        ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
          MaximumDegree G (Δ i) → HereditaryDensity G t (b i) →
            LeadingOne G (Δ i) t (b i) ζ Bₜ k) ∧
    -- K_{1,t,t}-free throughout t=o(log Δ/log log Δ).
    (∀ (Δ t : ℕ → ℕ), (∀ i, 1 ≤ Δ i ∧ 1 ≤ t i) →
      Filter.Tendsto Δ Filter.atTop Filter.atTop →
      Filter.Tendsto (fun i => (t i:ℝ)*Real.log (Real.log (Δ i))/Real.log (Δ i))
        Filter.atTop (nhds 0) →
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in Filter.atTop,
        ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
          MaximumDegree G (Δ i) → ApexFree G (t i) → LeadingOne G (Δ i) (t i) 0 ζ B k) ∧
    -- Rational b: same full mathematical statement, with separately charged expected bit cost.
    (∀ t : ℕ, 1 ≤ t → ∃ Aₜ Rₜ Bₜ : ℝ, 0 < Aₜ ∧ 1 < Rₜ ∧ 0 < Bₜ ∧
      ∀ n Δ : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
      ∀ b : ℚ, 1 ≤ Δ → 0 ≤ b → MaximumDegree G Δ → HereditaryDensity G t b →
      Rₜ ≤ rho Δ t b → ∀ w : Fin n → List (Fin n),
      (∀ u, IsSweep (G.neighborFinset u) (w u)) → BitConclusion G Δ t b w Aₜ Bₜ k) ∧
    (∀ (Δ t : ℕ → ℕ) (b : ℕ → ℚ), Admissible Δ t (fun i => (b i:ℝ)) →
      ∀ᶠ i in Filter.atTop, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
        MaximumDegree G (Δ i) → HereditaryDensity G (t i) (b i) →
        ∀ w : Fin n → List (Fin n), (∀ u, IsSweep (G.neighborFinset u) (w u)) →
          BitConclusion G (Δ i) (t i) (b i) w (A*t i) B k) := by

  obtain ⟨B,hB,hbit⟩ := bit_regime_uniform
  let A : ℝ := 4*(16*Real.exp 1+3)+2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB0 : 0 < B := by linarith
  refine ⟨A,B,1000,hA,hB0,by decide,?_,?_,?_,?_,?_,?_⟩
  · intro t ht
    obtain ⟨R,hR,hreg⟩ := fixed_regime_threshold t ht
    refine ⟨A*t,R,B,by positivity,hR,hB0,?_⟩
    intro n Δ G inst b hΔ hb hmax hd hr w hw
    have hh := hreg Δ b hb hr
    have hex := exact_regime G hΔ ht hb hmax hd hh.1 hh.2 w hw
    exact exact_weaken G ht hb (by nlinarith [Real.exp_pos 1]) (by norm_num) hB (by decide) w hex
  · intro Δ t b hadm
    filter_upwards [growing_regime Δ t b hadm] with i hi
    intro n G inst hmax hd w hw
    have hex := exact_regime G (hadm.1 i).1 (hadm.1 i).2.1 (hadm.1 i).2.2 hmax hd hi.1 hi.2 w hw
    exact exact_weaken G (hadm.1 i).2.1 (hadm.1 i).2.2
      (by nlinarith [Real.exp_pos 1]) (by norm_num) hB (by decide) w hex
  · intro t ht Δ b hb hΔ hsub
    obtain ⟨Bₜ,hBₜ,hleading⟩ := subpoly_leading t ht Δ b hb hΔ hsub
    refine ⟨Bₜ,hBₜ,?_⟩
    intro ζ hζ
    filter_upwards [hleading ζ hζ] with i hi
    intro n G inst hmax hd
    exact leading_weaken G hBₜ.le le_rfl (by decide) (hi n G inst hmax hd)
  · intro Δ t hpos hΔ he ζ hζ
    filter_upwards [apex_leading Δ t hpos hΔ he ζ hζ] with i hi
    intro n G inst hmax hfree
    exact leading_weaken G (by norm_num) hB (by decide) (hi n G inst hmax hfree)
  · intro t ht
    obtain ⟨R,hR,hreg⟩ := fixed_regime_threshold t ht
    refine ⟨A*t,R,B,by positivity,hR,hB0,?_⟩
    intro n Δ G inst b hΔ hb hmax hd hr w hw
    have hb' : (0:ℝ) ≤ b := by exact_mod_cast hb
    have hh := hreg Δ b hb' hr
    exact hbit n Δ t G inst b hΔ ht hb hmax hd hh.1 hh.2 w hw
  · intro Δ t b hadm
    filter_upwards [growing_regime Δ t (fun i => (b i:ℝ)) hadm] with i hi
    intro n G inst hmax hd w hw
    have hb : (0:ℚ) ≤ b i := by
      have hb0 : (0:ℝ) ≤ (b i:ℝ) := (hadm.1 i).2.2
      exact_mod_cast hb0
    exact hbit n (Δ i) (t i) G inst (b i) (hadm.1 i).1 (hadm.1 i).2.1 hb hmax hd hi.1 hi.2 w hw
