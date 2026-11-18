-- Prove2me | solution 1 for LocalOccupancyIS.Glauber.rounded_finite_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:34:15.362929+00:00
-- url     : https://prove2.me/submissions/cbcf5afa-2c20-45a2-9c41-5db29934a95b

import Definitions.Def_LocalOccupancyIS_Glauber_Dynamics
import Theorems.Thm_SinkhornHall_lemma_1_1
import Definitions.Def_LocalOccupancyIS_Glauber_Parameters
import Definitions.Def_LocalOccupancyIS_Glauber_Execution
import Theorems.Thm_LocalOccupancyIS_Glauber_lemma_9
import Theorems.Thm_LocalOccupancyIS_Glauber_lemma_7
import Theorems.Thm_LocalOccupancyIS_Glauber_lemma_5
import Theorems.Thm_LocalOccupancyIS_Glauber_lemma_11
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

lemma heatBath_reversible (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (A : Finset V)
    (σ τ : State G) :
    HardCoreBochner.hcLaw G lam σ * heatBath G lam A σ τ =
      HardCoreBochner.hcLaw G lam τ * heatBath G lam A τ σ := by
  classical
  by_cases he : ∀ v ∉ A, τ.val v = σ.val v
  · have he' : ∀ v ∉ A, σ.val v = τ.val v := fun v hv => (he v hv).symm
    have hden : (∑ ζ : State G, if ∀ v ∉ A, ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0) =
        ∑ ζ : State G, if ∀ v ∉ A, ζ.val v = τ.val v then HardCoreBochner.hcLaw G lam ζ else 0 := by
      apply Finset.sum_congr rfl
      intro ζ _
      have hiff : (∀ v ∉ A, ζ.val v = σ.val v) ↔ ∀ v ∉ A, ζ.val v = τ.val v := by
        constructor
        · intro h v hv; exact (h v hv).trans (he' v hv)
        · intro h v hv; exact (h v hv).trans (he v hv)
      simp only [hiff]
    simp only [heatBath, if_pos he, if_pos he', hden]
    ring
  · have he' : ¬∀ v ∉ A, σ.val v = τ.val v :=
      fun h => he (fun v hv => (h v hv).symm)
    simp [heatBath, he, he']

lemma heatBath_stationary (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (A : Finset V) :
    push (HardCoreBochner.hcLaw G lam) (heatBath G lam A) = HardCoreBochner.hcLaw G lam := by
  ext τ
  change (∑ σ, HardCoreBochner.hcLaw G lam σ * heatBath G lam A σ τ) = _
  simp_rw [heatBath_reversible G lam A, ← Finset.mul_sum, (heatBath_stochastic G hlam A).2 τ, mul_one]

lemma word_stationary (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (w : List V) :
    push (HardCoreBochner.hcLaw G lam) (word G lam w) = HardCoreBochner.hcLaw G lam := by
  induction w with
  | nil => simp [word, push]
  | cons u w ih =>
    change push _ (P G lam u * word G lam w) = _
    rw [← push_push]
    simp only [P]
    rw [heatBath_stationary G hlam {u}, ih]

lemma point_mixture_expectation (G : SimpleGraph V) [DecidableRel G.Adj] (ν : State G → ℝ)
    (K : Matrix (State G) (State G) ℝ) (f : State G → ℝ) :
    expectation (push ν K) f = ∑ σ, ν σ * expectation (push (point σ) K) f := by
  rw [expectation_push]
  apply Finset.sum_congr rfl
  intro σ _
  simp [push, Matrix.vecMul, dotProduct, point, expectation]

lemma equilibrium_occupancy_bound (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) :
    p lam * Fintype.card V * (1+lam)^(-avgDegree G) ≤ occupiedMean G lam := by
  classical
  let w := (Finset.univ : Finset V).toList
  have hw : IsSweep Finset.univ w := ⟨Finset.nodup_toList _, by simp [w]⟩
  have hi (I : State G) : p lam * Fintype.card V * (1+lam)^(-avgDegree G) ≤
      expectation (push (point I) (word G lam (w++w))) (fun σ => size σ.val) := by
    have hh := LocalOccupancyIS.Glauber.lemma_9 G (avgDegree G) lam hlam le_rfl w w hw hw I
    exact hh.2.2.trans hh.2.1
  let π := HardCoreBochner.hcLaw G lam
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun I _ =>
    mul_le_mul_of_nonneg_left (hi I) (hcLaw_pos G hlam I).le)
  rw [← Finset.sum_mul, (hcLaw_dist G hlam).2, one_mul] at hh
  rw [← point_mixture_expectation, word_stationary G hlam] at hh
  exact hh

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

def available (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G) : Finset V :=
  (G.neighborFinset u).filter (fun v => ∀ z, z ∉ G.neighborFinset u → G.Adj v z → I.val z = false)

lemma available_subset (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G) :
    available G u I ⊆ G.neighborFinset u := Finset.filter_subset _ _

lemma blocked_false (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G)
    {v : V} (hv : v ∈ G.neighborFinset u) (ha : v ∉ available G u I) : I.val v = false := by
  classical
  have hn : ¬ ∀ z, z ∉ G.neighborFinset u → G.Adj v z → I.val z = false := by
    simpa only [available, Finset.mem_filter, hv, true_and] using ha
  push_neg at hn
  obtain ⟨z,hz,hvz,hI⟩ := hn
  have hh := I.property v z hvz
  cases he : I.val v <;> cases hez : I.val z <;> simp_all

lemma available_exterior_false (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G)
    {a v : V} (ha : a ∈ available G u I) (hv : v ∉ available G u I) (hav : G.Adj a v) :
    I.val v = false := by
  by_cases hN : v ∈ G.neighborFinset u
  · exact blocked_false G u I hN hv
  · exact (Finset.mem_filter.mp ha).2 v hN hav

def embedAvailable (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G)
    (σ : State (G.induce (↑(available G u I) : Set V))) : State G :=
  ⟨fun v => if hv : v ∈ available G u I then σ.val ⟨v,hv⟩ else I.val v, by
    intro v z hvz
    by_cases hv : v ∈ available G u I
    · by_cases hz : z ∈ available G u I
      · simpa [hv,hz] using σ.property ⟨v,hv⟩ ⟨z,hz⟩ hvz
      · simp [hv,hz,available_exterior_false G u I hv hz hvz]
    · by_cases hz : z ∈ available G u I
      · simp [hv,hz,available_exterior_false G u I hz hv hvz.symm]
      · simpa [hv,hz] using I.property v z hvz⟩

lemma embedAvailable_apply (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G)
    (σ : State (G.induce (↑(available G u I) : Set V))) (v : ↑(↑(available G u I) : Set V)) :
    (embedAvailable G u I σ).val v = σ.val v := by simp [embedAvailable, v.property]

lemma available_neighbors_empty (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G)
    (σ : State (G.induce (↑(available G u I) : Set V))) (v : ↑(↑(available G u I) : Set V)) :
    (∀ z ∈ G.neighborFinset v.val, (embedAvailable G u I σ).val z = false) ↔
    (∀ z ∈ (G.induce (↑(available G u I) : Set V)).neighborFinset v, σ.val z = false) := by
  constructor
  · intro h z hz
    rw [← embedAvailable_apply G u I σ z]
    exact h z (by simpa using hz)
  · intro h z hz
    by_cases ha : z ∈ available G u I
    · have hh := h ⟨z,ha⟩ (by simpa using hz)
      simpa [embedAvailable,ha] using hh
    · simp [embedAvailable,ha,available_exterior_false G u I v.property ha (by simpa using hz)]

lemma spinState_same (G : SimpleGraph V) [DecidableRel G.Adj] (I : State G) (v : V) (coin : Bool) :
    (spinState G I v coin).val v = (if ∀ z ∈ G.neighborFinset v, I.val z = false then coin else false) := by
  simp only [spinState, updateSpin, Function.update_self]

lemma embedAvailable_spin (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G)
    (σ : State (G.induce (↑(available G u I) : Set V))) (v : ↑(↑(available G u I) : Set V)) (coin : Bool) :
    spinState G (embedAvailable G u I σ) v.val coin =
      embedAvailable G u I (spinState (G.induce (↑(available G u I) : Set V)) σ v coin) := by
  apply Subtype.ext
  funext z
  by_cases hz : z = v.val
  · subst z
    rw [spinState_same, embedAvailable_apply, spinState_same]
    simp only [available_neighbors_empty]
  · by_cases ha : z ∈ available G u I
    · have hza : (⟨z,ha⟩ : ↑(↑(available G u I) : Set V)) ≠ v := by intro hh; exact hz (congrArg Subtype.val hh)
      simp [spinState,updateSpin,Function.update_of_ne hz,embedAvailable,ha,Function.update_of_ne hza]
    · simp [spinState,updateSpin,Function.update_of_ne hz,embedAvailable,ha]

lemma embedAvailable_blocked_spin (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G)
    (σ : State (G.induce (↑(available G u I) : Set V))) {v : V}
    (hv : v ∈ G.neighborFinset u) (ha : v ∉ available G u I) (coin : Bool) :
    spinState G (embedAvailable G u I σ) v coin = embedAvailable G u I σ := by
  classical
  have hn : ¬ ∀ z, z ∉ G.neighborFinset u → G.Adj v z → I.val z = false := by
    simpa only [available,Finset.mem_filter,hv,true_and] using ha
  push_neg at hn
  obtain ⟨z,hz,hvz,hI⟩ := hn
  have hzA : z ∉ available G u I := fun hh => hz (available_subset G u I hh)
  have hblocked : ¬ ∀ z ∈ G.neighborFinset v, (embedAvailable G u I σ).val z = false := by
    intro h
    have hh := h z (by simpa using hvz)
    apply hI
    simpa [embedAvailable,hzA] using hh
  apply Subtype.ext
  funext z
  by_cases he : z = v
  · subst z
    rw [spinState_same, if_neg hblocked]
    simp [embedAvailable,ha,blocked_false G u I hv ha]
  · simp [spinState,updateSpin,Function.update_of_ne he]

lemma point_word_cons (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (I : State G) (v : V) (w : List V) (f : State G → ℝ) :
    expectation (push (point I) (word G lam (v::w))) f =
      p lam*expectation (push (point (spinState G I v true)) (word G lam w)) f +
      (1-p lam)*expectation (push (point (spinState G I v false)) (word G lam w)) f := by
  have he : word G lam (v::w) = P G lam v*word G lam w := by simp [word]
  rw [he, ← push_push, point_mixture_expectation, point_push]
  exact single_site_average G hlam I v _

def restrictWord (A : Finset V) (w : List V) : List (↑(↑A : Set V)) :=
  w.filterMap (fun v => if hv : v ∈ A then some ⟨v,hv⟩ else none)

lemma embedAvailable_word (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (u : V) (I : State G) (w : List V)
    (hw : ∀ v ∈ w, v ∈ G.neighborFinset u)
    (σ : State (G.induce (↑(available G u I) : Set V))) (f : State G → ℝ) :
    expectation (push (point (embedAvailable G u I σ)) (word G lam w)) f =
      expectation (push (point σ) (word (G.induce (↑(available G u I) : Set V)) lam
        (restrictWord (available G u I) w))) (fun τ => f (embedAvailable G u I τ)) := by
  induction w generalizing σ with
  | nil => simp [restrictWord,word,point_push,expectation,Matrix.one_apply]
  | cons v w ih =>
    have hv := hw v (by simp)
    have htail : ∀ v ∈ w, v ∈ G.neighborFinset u := fun v hv => hw v (by simp [hv])
    by_cases ha : v ∈ available G u I
    · simp only [restrictWord,List.filterMap_cons,dif_pos ha]
      rw [point_word_cons G hlam, point_word_cons _ hlam]
      rw [embedAvailable_spin G u I σ ⟨v,ha⟩ true, embedAvailable_spin G u I σ ⟨v,ha⟩ false]
      change p lam*expectation (push (point (embedAvailable G u I _)) (word G lam w)) f +
        (1-p lam)*expectation (push (point (embedAvailable G u I _)) (word G lam w)) f = _
      rw [ih htail, ih htail]
      rfl
    · simp only [restrictWord,List.filterMap_cons,dif_neg ha]
      rw [point_word_cons G hlam]
      simp_rw [embedAvailable_blocked_spin G u I _ hv ha]
      rw [ih htail]
      simp only [restrictWord]
      ring

lemma restrictWord_sweep {A N : Finset V} (hA : A ⊆ N) (w : List V) (hw : IsSweep N w) :
    IsSweep Finset.univ (restrictWord A w) := by
  classical
  constructor
  · apply List.Nodup.filterMap _ hw.1
    intro a a' z ha ha'
    simp only [Option.mem_def] at ha ha'
    split_ifs at ha ha' with h h'
    all_goals simp only [Option.some.injEq, reduceCtorEq] at ha ha'
    exact (congrArg Subtype.val ha).trans (congrArg Subtype.val ha').symm
  · ext v
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true,restrictWord,List.mem_filterMap]
    refine ⟨v.val,?_,?_⟩
    · rw [← List.mem_toFinset,hw.2]
      exact hA v.property
    · simp [v.property]

def restrictInitial (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G) :
    State (G.induce (↑(available G u I) : Set V)) :=
  ⟨fun v => I.val v, fun v z hvz => I.property v z hvz⟩

lemma embedAvailable_initial (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G) :
    embedAvailable G u I (restrictInitial G u I) = I := by
  apply Subtype.ext
  funext v
  simp [embedAvailable,restrictInitial]

lemma embedAvailable_nbrSize (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (I : State G)
    (σ : State (G.induce (↑(available G u I) : Set V))) :
    nbrSize G u (embedAvailable G u I σ).val = size σ.val := by
  classical
  have he : (nbrSize G u (embedAvailable G u I σ).val:ℝ) = (size σ.val:ℝ) := by
    rw [nbrSize_sum, size_sum]
    have hsub := Finset.sum_subtype (p := fun v => v ∈ (↑(available G u I) : Set V)) (F := inferInstance) (available G u I) (fun _ => Iff.rfl)
      (fun v => if (embedAvailable G u I σ).val v = true then (1:ℝ) else 0)
    simp only [embedAvailable_apply] at hsub
    rw [← hsub]
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro v hv
      simpa using available_subset G u I hv
    · intro v hv hnot
      have hn : v ∈ G.neighborFinset u := by simpa using hv
      simp [embedAvailable,hnot,blocked_false G u I hn hnot]
  exact_mod_cast he

lemma available_score_transport (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (β γ : ℝ) (u : V) (I : State G) (w : List V)
    (hw : ∀ v ∈ w, v ∈ G.neighborFinset u) :
    expectation (push (point I) (word G lam w)) (score G lam β γ u) =
      expectation (push (point (restrictInitial G u I))
        (word (G.induce (↑(available G u I) : Set V)) lam (restrictWord (available G u I) w)))
        (fun σ => β*p lam*(if size σ.val = 0 then 1 else 0)+γ*size σ.val) := by
  have hh := embedAvailable_word G hlam u I w hw (restrictInitial G u I) (score G lam β γ u)
  rw [embedAvailable_initial] at hh
  rw [hh]
  apply congrArg
  funext σ
  simp only [score,embedAvailable_nbrSize]

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

lemma partition_eq_full (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) :
    partition G lam = ∑ σ : V → Bool, MarkovMixing.hardcoreWeight G lam σ := by
  classical
  unfold partition
  calc
    _ = ∑ σ ∈ Finset.univ.filter (MarkovMixing.IsHardcore G), lam ^ size σ :=
      (Finset.sum_subtype _ (by simp) _).symm
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro σ _
      rfl

lemma partition_pos (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam) :
    0 < partition G lam := by rw [partition_eq_full]; exact hcPartition_pos G hlam

lemma hcLaw_partition (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (σ : State G) :
    HardCoreBochner.hcLaw G lam σ = lam ^ size σ.val / partition G lam := by
  rw [partition_eq_full]
  simp [HardCoreBochner.hcLaw, MarkovMixing.hardcoreDist, MarkovMixing.hardcoreWeight, σ.property, size]

lemma occupiedMean_ratio (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) :
    occupiedMean G lam = (∑ σ : State G, (size σ.val : ℝ)*lam^size σ.val) / partition G lam := by
  unfold occupiedMean expectation
  simp_rw [hcLaw_partition, div_mul_eq_mul_div, mul_comm (lam ^ _) (size _ : ℝ)]
  rw [Finset.sum_div]

lemma power_cross_nonneg {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (a b : ℕ) :
    0 ≤ ((a:ℝ)-b)*(y^a*x^b-x^a*y^b) := by
  have hy : 0 < y := hx.trans_le hxy
  rcases le_total a b with hab | hba
  · obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hab
    have hpow : x^c ≤ y^c := pow_le_pow_left₀ hx.le hxy c
    have hcross : y^a*x^(a+c)-x^a*y^(a+c) ≤ 0 := by
      calc
        _ = x^a*y^a*(x^c-y^c) := by rw [pow_add, pow_add]; ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hpow)
    exact mul_nonneg_of_nonpos_of_nonpos (by push_cast; linarith : (a:ℝ)-(a+c:ℕ) ≤ 0) hcross
  · obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hba
    have hpow : x^c ≤ y^c := pow_le_pow_left₀ hx.le hxy c
    have hcross : 0 ≤ y^(b+c)*x^b-x^(b+c)*y^b := by
      calc
        _ = x^b*y^b*(y^c-x^c) := by rw [pow_add, pow_add]; ring
        _ ≥ 0 := mul_nonneg (by positivity) (sub_nonneg.mpr hpow)
    exact mul_nonneg (by push_cast; linarith : (0:ℝ) ≤ (b+c:ℕ)-b) hcross

lemma finite_gibbs_comparison {Ω : Type} [Fintype Ω] (f : Ω → ℕ)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (∑ i, (f i:ℝ)*x^(f i)) * (∑ i, y^(f i)) ≤
      (∑ i, (f i:ℝ)*y^(f i)) * (∑ i, x^(f i)) := by
  have hh : 0 ≤ ∑ i : Ω, ∑ j : Ω,
      ((f i:ℝ)-f j)*(y^(f i)*x^(f j)-x^(f i)*y^(f j)) := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg (fun j _ => power_cross_nonneg hx hxy (f i) (f j))
  have he : (∑ i : Ω, ∑ j : Ω,
      ((f i:ℝ)-f j)*(y^(f i)*x^(f j)-x^(f i)*y^(f j))) =
      2*((∑ i, (f i:ℝ)*y^(f i))*(∑ i,x^(f i)) -
        (∑ i,(f i:ℝ)*x^(f i))*(∑ i,y^(f i))) := by
    calc
      _ = ∑ i : Ω, ∑ j : Ω,
          (((f i:ℝ)*y^(f i))*x^(f j) - ((f i:ℝ)*x^(f i))*y^(f j) -
           y^(f i)*((f j:ℝ)*x^(f j)) + x^(f i)*((f j:ℝ)*y^(f j))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
  rw [he] at hh
  linarith

lemma occupiedMean_mono (G : SimpleGraph V) [DecidableRel G.Adj] {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) : occupiedMean G x ≤ occupiedMean G y := by
  rw [occupiedMean_ratio, occupiedMean_ratio]
  apply (div_le_div_iff₀ (partition_pos G hx) (partition_pos G (hx.trans_le hxy))).mpr
  exact finite_gibbs_comparison (fun σ : State G => size σ.val) hx hxy

lemma avgDegree_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] : 0 ≤ avgDegree G := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (Nat.cast_nonneg _)

lemma log_partition_upper (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam) :
    Real.log (partition G lam) ≤ Fintype.card V*lam := by
  have hp : 0 < 1+lam := by positivity
  have hZ : partition G lam ≤ (1+lam)^Fintype.card V := by rw [partition_eq_full]; exact partition_upper G hlam
  have hh := Real.log_le_log (partition_pos G hlam) hZ
  rw [Real.log_pow] at hh
  have hlog : Real.log (1+lam) ≤ lam := by
    have h := Real.log_le_sub_one_of_pos hp
    linarith
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  exact hh.trans hm

lemma occupancy_exp_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam) :
    lam*Fintype.card V*Real.exp (-(avgDegree G+1)*lam) ≤ occupiedMean G lam := by
  have hp : 0 < 1+lam := by positivity
  have hd : 0 ≤ avgDegree G+1 := by linarith [avgDegree_nonneg G]
  have heq : p lam*Fintype.card V*(1+lam)^(-avgDegree G) =
      lam*Fintype.card V*Real.exp (-(avgDegree G+1)*Real.log (1+lam)) := by
    have hex : -(avgDegree G+1)*Real.log (1+lam) =
        Real.log (1+lam)*(-avgDegree G) + -Real.log (1+lam) := by ring
    rw [hex, Real.exp_add, Real.exp_neg, Real.exp_log hp, Real.rpow_def_of_pos hp]
    unfold p
    ring
  have hlog : Real.log (1+lam) ≤ lam := by
    have h := Real.log_le_sub_one_of_pos hp
    linarith
  have hex := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hd))
  have hm := mul_le_mul_of_nonneg_left hex (show 0 ≤ lam*Fintype.card V by positivity)
  rw [← heq] at hm
  exact hm.trans (equilibrium_occupancy_bound G hlam)

lemma occupancy_min_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam) :
    (1/Real.exp 1) * min (lam*Fintype.card V) (Fintype.card V/(avgDegree G+1)) ≤ occupiedMean G lam := by
  let y := min lam (1/(avgDegree G+1))
  have hd : 0 < avgDegree G+1 := by linarith [avgDegree_nonneg G]
  have hy : 0 < y := lt_min hlam (by positivity)
  have hylam : y ≤ lam := min_le_left _ _
  have hyd : (avgDegree G+1)*y ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right lam (1/(avgDegree G+1))) hd.le
    simpa [y, hd.ne'] using hh
  have hex : Real.exp (-1) ≤ Real.exp (-(avgDegree G+1)*y) := Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left hex (show 0 ≤ y*Fintype.card V by positivity)
  have hh := hm.trans ((occupancy_exp_lower G hy).trans (occupiedMean_mono G hy hylam))
  have heq : y*Fintype.card V*Real.exp (-1) =
      (1/Real.exp 1) * min (lam*Fintype.card V) (Fintype.card V/(avgDegree G+1)) := by
    dsimp [y]
    rw [Real.exp_neg, min_mul_of_nonneg _ _ (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)]
    simp [div_eq_mul_inv, mul_comm]
  rw [heq] at hh
  exact hh

lemma partition_empty (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (hk : Fintype.card V = 0) :
    partition G lam = 1 := by
  haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hk
  simp [partition, size]
  exact Fintype.card_eq_one_iff.mpr ⟨(⟨_,empty_hardcore G⟩ : State G), fun _ => Subsingleton.elim _ _⟩

lemma occupiedMean_empty (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (hk : Fintype.card V = 0) :
    occupiedMean G lam = 0 := by
  haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hk
  simp [occupiedMean, expectation, size]

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma cutoff_div_scale {Δ b : ℝ} {t : ℕ} (hb : 0 ≤ b) :
    cutoff Δ t b/scale t b = 4*Real.exp 1*D Δ t b^(2*t) := by
  unfold cutoff
  field_simp [(scale_pos t hb).ne']
  <;> ring

lemma cutoff_ge_scale {Δ b : ℝ} {t : ℕ} (hb : 0 ≤ b) (hD : 1 ≤ D Δ t b) :
    scale t b ≤ cutoff Δ t b := by
  have hs := scale_pos t hb
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hpow : 1 ≤ D Δ t b^(2*t) := one_le_pow₀ hD
  unfold cutoff
  have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4*Real.exp 1*scale t b by positivity)
  nlinarith

lemma degree_parameter_identity {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 0 < D Δ t b) :
    4*(t:ℝ)*fugacity Δ t b*scale t b*(cutoff Δ t b/scale t b)^(1-1/(t:ℝ)) =
      4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b := by
  have hs := scale_pos t hb
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have hr : ((2*t-1:ℕ):ℝ) = 2*(t:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*t)]
    norm_num
  rw [cutoff_div_scale hb]
  unfold fugacity
  apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Real.log_one]
  rw [hr]
  push_cast
  field_simp
  <;> ring

lemma small_graph_degree_bound {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {Δ b : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hk : 1 ≤ Fintype.card V) (hd : Density F t b) (hsmall : (Fintype.card V:ℝ) ≤ cutoff Δ t b) :
    fugacity Δ t b*(avgDegree F+1) ≤
      4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hs := scale_pos t hb
  have hD0 := (D_large_basic ht hD).2.1
  have hD1 := (D_large_basic ht hD).2.2
  have hlam := fugacity_pos hb hD0
  have ha : 0 ≤ 1-1/(t:ℝ) := by
    have hh : 1/(t:ℝ) ≤ 1 := (div_le_one (by linarith : (0:ℝ) < t)).mpr ht'
    linarith
  have hdeg := (LocalOccupancyIS.Glauber.lemma_5 F t ht b hb hk hd 0 (fun _ => 0) (by simp)).2
  have hM : 1 ≤ cutoff Δ t b/scale t b := (le_div_iff₀ hs).mpr (by simpa using cutoff_ge_scale hb hD1)
  have hmax : max 1 (((Fintype.card V:ℝ)/scale t b)^(1-1/(t:ℝ))) ≤
      (cutoff Δ t b/scale t b)^(1-1/(t:ℝ)) := by
    apply max_le
    · exact Real.one_le_rpow hM ha
    · exact Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) hs.le)
        (div_le_div_of_nonneg_right hsmall hs.le) ha
  have hm := mul_le_mul_of_nonneg_left hmax (show 0 ≤ 4*(t:ℝ)*scale t b by positivity)
  have hm' := mul_le_mul_of_nonneg_left (hdeg.trans hm) hlam.le
  calc
    _ ≤ fugacity Δ t b*(4*(t:ℝ)*scale t b*(cutoff Δ t b/scale t b)^(1-1/(t:ℝ))) := hm'
    _ = _ := by rw [← degree_parameter_identity ht hb hD0]; ring

lemma small_graph_occupancy {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {Δ b : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hk : 1 ≤ Fintype.card V) (hd : Density F t b) (hsmall : (Fintype.card V:ℝ) ≤ cutoff Δ t b) :
    correction Δ t b*fugacity Δ t b*Fintype.card V ≤ occupiedMean F (fugacity Δ t b) := by
  have hD0 := (D_large_basic ht hD).2.1
  have hlam := fugacity_pos hb hD0
  have hh := small_graph_degree_bound F ht hb hD hk hd hsmall
  have he := Real.exp_le_exp.mpr (neg_le_neg hh)
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ fugacity Δ t b*Fintype.card V by positivity)
  have heq : Real.exp (-(fugacity Δ t b*(avgDegree F+1))) =
      Real.exp (-(avgDegree F+1)*fugacity Δ t b) := by congr 1; ring
  rw [heq] at hm
  have h := hm.trans (occupancy_exp_lower F hlam)
  simpa only [correction, mul_comm, mul_left_comm, mul_assoc] using h

lemma fugacity_cutoff {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 0 < D Δ t b) :
    fugacity Δ t b*cutoff Δ t b = 4*Real.exp 1*D Δ t b := by
  have hp : D Δ t b^(2*t) = D Δ t b^(2*t-1)*D Δ t b := by
    rw [← pow_succ]
    congr 1
    omega
  unfold fugacity cutoff
  rw [hp]
  field_simp [(scale_pos t hb).ne', (pow_pos hD (2*t-1)).ne']
  <;> ring

lemma degree_ratio_identity {k s T : ℝ} (hk : 0 < k) (hs : 0 < s) (hT : 0 < T) :
    k/(4*T*s*(k/s)^(1-1/T)) = (k/s)^(1/T)/(4*T) := by
  apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  ring

lemma large_graph_occupancy {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {Δ b : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hk : 1 ≤ Fintype.card V) (hd : Density F t b) (hlarge : cutoff Δ t b ≤ (Fintype.card V:ℝ)) :
    2*D Δ t b ≤ occupiedMean F (fugacity Δ t b) := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0:ℝ) < t := by linarith
  have hs := scale_pos t hb
  have hD0 := (D_large_basic ht hD).2.1
  have hD1 := (D_large_basic ht hD).2.2
  have hlam := fugacity_pos hb hD0
  have hK : (0:ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hKs : 1 ≤ (Fintype.card V:ℝ)/scale t b := (le_div_iff₀ hs).mpr
    (by simpa using (cutoff_ge_scale hb hD1).trans hlarge)
  have ha : 0 ≤ 1-1/(t:ℝ) := by
    have hh := (div_le_one ht0).mpr ht'
    linarith
  have hpow1 := Real.one_le_rpow hKs ha
  have hdeg := (LocalOccupancyIS.Glauber.lemma_5 F t ht b hb hk hd 0 (fun _ => 0) (by simp)).2
  change avgDegree F+1 ≤ 4*(t:ℝ)*scale t b*max 1 (((Fintype.card V:ℝ)/scale t b)^(1-1/(t:ℝ))) at hdeg
  rw [max_eq_right hpow1] at hdeg
  have hratio : (cutoff Δ t b/scale t b)^(1/(t:ℝ))/(4*t) ≤
      (Fintype.card V:ℝ)/(avgDegree F+1) := by
    have hR := Real.rpow_le_rpow
      (div_nonneg (le_trans hs.le (cutoff_ge_scale hb hD1)) hs.le)
      (div_le_div_of_nonneg_right hlarge hs.le) (show 0 ≤ 1/(t:ℝ) by positivity)
    have hR' := div_le_div_of_nonneg_right hR (show 0 ≤ 4*(t:ℝ) by positivity)
    have hd0 : 0 < avgDegree F+1 := by linarith [avgDegree_nonneg F]
    have hi := div_le_div_of_nonneg_left hK.le hd0 hdeg
    rw [degree_ratio_identity hK hs ht0] at hi
    exact hR'.trans hi
  have hcut : (cutoff Δ t b/scale t b)^(1/(t:ℝ)) =
      (4*Real.exp 1)^(1/(t:ℝ))*D Δ t b^2 := by
    rw [cutoff_div_scale hb, Real.mul_rpow (by positivity) (pow_nonneg hD0.le _), ← Real.rpow_natCast_mul hD0.le]
    have he : (2*t:ℕ)*(1/(t:ℝ)) = (2:ℝ) := by push_cast; field_simp
    rw [he, Real.rpow_two]
  rw [hcut] at hratio
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hcbase : 1 ≤ (4*Real.exp 1)^(1/(t:ℝ)) := Real.one_le_rpow (by linarith) (by positivity)
  have hratio2 : 2*Real.exp 1*D Δ t b ≤ (Fintype.card V:ℝ)/(avgDegree F+1) := by
    have hDmul := mul_le_mul_of_nonneg_right hD hD0.le
    have hpowmul := mul_le_mul_of_nonneg_right hcbase (sq_nonneg (D Δ t b))
    have hr := (div_le_iff₀ (show (0:ℝ) < 4*t by positivity)).mp hratio
    nlinarith
  have hLam : 2*Real.exp 1*D Δ t b ≤ fugacity Δ t b*Fintype.card V := by
    have hh := mul_le_mul_of_nonneg_left hlarge hlam.le
    rw [fugacity_cutoff ht hb hD0] at hh
    nlinarith [Real.exp_pos 1]
  have hmin := le_min hLam hratio2
  have hh := mul_le_mul_of_nonneg_left hmin (show 0 ≤ 1/Real.exp 1 by positivity)
  have heq : 1/Real.exp 1*(2*Real.exp 1*D Δ t b) = 2*D Δ t b := by field_simp
  rw [heq] at hh
  exact hh.trans (occupancy_min_lower F hlam)

lemma occupancy_tangent {lam c w Z E : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hw : 0 ≤ w) (hZ : 0 < Z) (hE : c*Real.log Z ≤ E) :
    1 ≤ beta lam w*p lam/Z + gamma c w*E := by
  have hp : 0 < p lam := div_pos hlam (by positivity)
  have hw1 : 0 < 1+w := by linarith
  have hmain : 1 ≤ (Real.exp (w-Real.log Z)+Real.log Z)/(1+w) := by
    apply (le_div_iff₀ hw1).mpr
    have hh := Real.add_one_le_exp (w-Real.log Z)
    linarith
  have hm := mul_le_mul_of_nonneg_left hE (show 0 ≤ 1/(c*(1+w)) by positivity)
  have heq : beta lam w*p lam/Z = Real.exp (w-Real.log Z)/(1+w) := by
    unfold beta
    rw [Real.exp_sub, Real.exp_log hZ]
    field_simp
    <;> ring
  rw [heq]
  unfold gamma
  have hcancel : 1/(c*(1+w))*(c*Real.log Z) = Real.log Z/(1+w) := by field_simp
  rw [hcancel] at hm
  rw [add_div] at hmain
  linarith

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma sweep_decomposition (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (w : List V) (hw : IsSweep Finset.univ w) (v : V) :
    ∃ pre post : List V, w = pre ++ v :: post ∧ v ∉ post ∧
      expectation (push ν (word G lam w)) (fun σ => if σ.val v = true then (1:ℝ) else 0) =
      p lam * expectation (push ν (word G lam pre)) (fun σ => if nbrSize G v σ.val = 0 then 1 else 0) := by
  classical
  have hv : v ∈ w := by rw [← List.mem_toFinset, hw.2]; exact Finset.mem_univ _
  obtain ⟨pre,post,he⟩ := List.mem_iff_append.mp hv
  have hpost : v ∉ post := by
    have hh := hw.1
    rw [he] at hh
    exact (List.nodup_cons.mp (List.nodup_append.mp hh).2.1).1
  refine ⟨pre,post,he,hpost,?_⟩
  have he' : w = (pre++[v])++post := by rw [he]; simp
  rw [he', word_append, ← push_push, site_word_outside G hlam _ post hpost,
    word_append, ← push_push]
  simp only [word, List.map_singleton, List.prod_singleton]
  exact expected_site_occupancy G hlam _ v

lemma expectation_nonneg {Ω : Type} [Fintype Ω] {ν : Ω → ℝ}
    (hν : MarkovMixing.IsDist ν) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ expectation ν f := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hν.1 x) (hf x))

lemma expectation_indicator_le_one {Ω : Type} [Fintype Ω] {ν : Ω → ℝ}
    (hν : MarkovMixing.IsDist ν) (E : Ω → Prop) [DecidablePred E] :
    expectation ν (fun x => if E x then (1:ℝ) else 0) ≤ 1 := by
  calc
    _ ≤ ∑ x, ν x := by
      apply Finset.sum_le_sum
      intro x _
      change ν x * (if E x then (1:ℝ) else 0) ≤ ν x
      split_ifs
      · simp
      · simpa using hν.1 x
    _ = 1 := hν.2

lemma sweep_marginal_range (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν)
    (w : List V) (hw : IsSweep Finset.univ w) (v : V) :
    0 ≤ expectation (push ν (word G lam w)) (fun σ => if σ.val v = true then (1:ℝ) else 0) ∧
    expectation (push ν (word G lam w)) (fun σ => if σ.val v = true then (1:ℝ) else 0) ≤ p lam := by
  classical
  constructor
  · exact expectation_nonneg (push_dist hν (word_stochastic G hlam w)) (by intro σ; split_ifs <;> norm_num)
  · obtain ⟨pre,post,he,hpost,hh⟩ := sweep_decomposition G hlam ν w hw v
    rw [hh]
    have hh' := mul_le_mul_of_nonneg_left
      (expectation_indicator_le_one (push_dist hν (word_stochastic G hlam pre))
        (fun σ : State G => nbrSize G v σ.val = 0)) (p_pos hlam).le
    simpa using hh'

lemma cut_marginal_bound (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν)
    (pre post : List V) (hw : (pre++post).Nodup) (u : V) :
    expectation (push ν (word G lam pre)) (fun σ => if σ.val u = true then (1:ℝ) else 0) ≤
      expectation ν (fun σ => if σ.val u = true then (1:ℝ) else 0) +
      expectation (push ν (word G lam (pre++post))) (fun σ => if σ.val u = true then (1:ℝ) else 0) := by
  classical
  by_cases hu : u ∈ pre
  · have hpost : u ∉ post := List.disjoint_left.mp (List.nodup_append'.mp hw).2.2 hu
    rw [word_append, ← push_push, site_word_outside G hlam _ post hpost]
    have hh := expectation_nonneg hν (f := fun σ => if σ.val u = true then (1:ℝ) else 0)
      (by intro σ; split_ifs <;> norm_num)
    linarith
  · rw [site_word_outside G hlam _ pre hu]
    have hh := expectation_nonneg (push_dist hν (word_stochastic G hlam (pre++post)))
      (f := fun σ => if σ.val u = true then (1:ℝ) else 0) (by intro σ; split_ifs <;> norm_num)
    linarith

lemma probability_empty_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) (v : V) :
    1-expectation ν (fun σ => nbrSize G v σ.val) ≤
      expectation ν (fun σ => if nbrSize G v σ.val = 0 then (1:ℝ) else 0) := by
  have hpoint (σ : State G) : 1-(nbrSize G v σ.val : ℝ) ≤
      if nbrSize G v σ.val = 0 then (1:ℝ) else 0 := by
    split_ifs with hz
    · simp [hz]
    · have hh : 1 ≤ nbrSize G v σ.val := Nat.one_le_iff_ne_zero.mpr hz
      have hh' : (1:ℝ) ≤ nbrSize G v σ.val := by exact_mod_cast hh
      linarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun σ _ =>
    mul_le_mul_of_nonneg_left (hpoint σ) (hν.1 σ))
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib] at hh
  rw [hν.2] at hh
  exact hh

lemma expected_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : State G → ℝ) (v : V) :
    expectation ν (fun σ => nbrSize G v σ.val) =
      ∑ u, if G.Adj v u then expectation ν (fun σ => if σ.val u = true then (1:ℝ) else 0) else 0 := by
  classical
  unfold expectation
  simp_rw [nbrSize_sum, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : G.Adj v u <;> simp [hu]

lemma neighbors_double_count (G : SimpleGraph V) [DecidableRel G.Adj] (a : V → ℝ) :
    (∑ v, ∑ u, if G.Adj v u then a u else 0) = ∑ u, (G.degree u : ℝ)*a u := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  have he : (∑ v, if G.Adj v u then (1:ℝ) else 0) = G.degree u := by
    simp_rw [G.adj_comm (v := u)]
    rw [← Finset.sum_filter]
    simp [← SimpleGraph.mem_neighborFinset]
  rw [← he, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

lemma expectation_size_sum (G : SimpleGraph V) [DecidableRel G.Adj] (ν : State G → ℝ) :
    expectation ν (fun σ => size σ.val) =
      ∑ v, expectation ν (fun σ => if σ.val v = true then (1:ℝ) else 0) := by
  unfold expectation
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← size_sum]

lemma sweep_union_bound (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν)
    (w : List V) (hw : IsSweep Finset.univ w) :
    p lam*Fintype.card V - p lam * ∑ u, (G.degree u : ℝ) *
      (expectation ν (fun σ => if σ.val u = true then (1:ℝ) else 0) +
       expectation (push ν (word G lam w)) (fun σ => if σ.val u = true then (1:ℝ) else 0)) ≤
      expectation (push ν (word G lam w)) (fun σ => size σ.val) := by
  classical
  have hvertex (v : V) : p lam * (1- ∑ u, if G.Adj v u then
      expectation ν (fun σ => if σ.val u = true then (1:ℝ) else 0) +
      expectation (push ν (word G lam w)) (fun σ => if σ.val u = true then (1:ℝ) else 0) else 0) ≤
      expectation (push ν (word G lam w)) (fun σ => if σ.val v = true then (1:ℝ) else 0) := by
    obtain ⟨pre,post,he,hpost,hh⟩ := sweep_decomposition G hlam ν w hw v
    rw [hh]
    have hνpre := push_dist hν (word_stochastic G hlam pre)
    have hn : expectation (push ν (word G lam pre)) (fun σ => nbrSize G v σ.val) ≤
        ∑ u, if G.Adj v u then
          expectation ν (fun σ => if σ.val u = true then (1:ℝ) else 0) +
          expectation (push ν (word G lam w)) (fun σ => if σ.val u = true then (1:ℝ) else 0) else 0 := by
      rw [expected_neighbors]
      apply Finset.sum_le_sum
      intro u _
      split_ifs
      · have hh' := cut_marginal_bound G hlam ν hν pre (v::post) (he ▸ hw.1) u
        simpa only [← he] using hh'
      · rfl
    have hb := probability_empty_lower G (push ν (word G lam pre)) hνpre v
    exact mul_le_mul_of_nonneg_left (by linarith : _ ≤ _) (p_pos hlam).le
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hvertex v)
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  rw [neighbors_double_count, ← expectation_size_sum] at hh
  simpa [mul_comm] using hh

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma fraction_rpow_mono {x y q a : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hq : 0 ≤ q)
    (ha : a ≤ 1) : x/(1+q*x^a) ≤ y/(1+q*y^a) := by
  have hy : 0 < y := hx.trans_le hxy
  have hh := Real.rpow_le_rpow_of_nonpos hx hxy (by linarith : a-1 ≤ 0)
  rw [Real.rpow_sub_one hy.ne', Real.rpow_sub_one hx.ne'] at hh
  have hc : x*y^a ≤ y*x^a := by
    have h := (div_le_div_iff₀ hy hx).mp hh
    nlinarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hc hq]

lemma sweep_large_constants {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 1000*Real.exp 1*t ≤ D Δ t b) :
    8*t*scale t b*p (fugacity Δ t b) ≤ 1/8 ∧
    4*t*p (fugacity Δ t b)*(scale t b)^(1/(t:ℝ))*(cutoff Δ t b)^(1-1/(t:ℝ)) ≤ 1/8 ∧
    (32/9)*Real.exp 1*D Δ t b ≤ p (fugacity Δ t b)*cutoff Δ t b := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hDsmall : 8*Real.exp 1*t ≤ D Δ t b := by nlinarith [Real.exp_pos 1]
  have hD0 := (D_large_basic ht hDsmall).2.1
  have hD1 := (D_large_basic ht hDsmall).2.2
  have hs := scale_pos t hb
  have hMp : 0 < cutoff Δ t b := hs.trans_le (cutoff_ge_scale hb hD1)
  have hlam := fugacity_pos hb hD0
  have hpLam : p (fugacity Δ t b) ≤ fugacity Δ t b := by
    unfold p
    exact div_le_self hlam.le (by linarith)
  have hsp : scale t b*p (fugacity Δ t b) ≤ 1/D Δ t b := by
    have hh := mul_le_mul_of_nonneg_left hpLam hs.le
    have hr : D Δ t b ≤ D Δ t b^(2*t-1) := le_self_pow₀ hD1 (by omega)
    have hi := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hD0 hr
    have heq : scale t b*fugacity Δ t b = 1/D Δ t b^(2*t-1) := by unfold fugacity; field_simp
    rw [heq] at hh
    exact hh.trans hi
  have htD : (t:ℝ)/D Δ t b ≤ 1/1000 := by
    apply (div_le_iff₀ hD0).mpr
    nlinarith
  have hfirst : 8*t*scale t b*p (fugacity Δ t b) ≤ 1/8 := by
    have hh := mul_le_mul_of_nonneg_left hsp (show 0 ≤ 8*(t:ℝ) by positivity)
    have heq : 8*(t:ℝ)*(1/D Δ t b) = 8*((t:ℝ)/D Δ t b) := by ring
    rw [heq] at hh
    nlinarith
  have hpident : (scale t b)^(1/(t:ℝ))*(cutoff Δ t b)^(1-1/(t:ℝ)) =
      scale t b*(cutoff Δ t b/scale t b)^(1-1/(t:ℝ)) := by
    apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
    simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_rpow]
    ring
  have hsecond : 4*t*p (fugacity Δ t b)*(scale t b)^(1/(t:ℝ))*(cutoff Δ t b)^(1-1/(t:ℝ)) ≤ 1/8 := by
    have hh := mul_le_mul_of_nonneg_right hpLam (show 0 ≤ 4*(t:ℝ)*((scale t b)^(1/(t:ℝ))*(cutoff Δ t b)^(1-1/(t:ℝ))) by positivity)
    have heq : 4*(t:ℝ)*fugacity Δ t b*((scale t b)^(1/(t:ℝ))*(cutoff Δ t b)^(1-1/(t:ℝ))) =
        4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b := by rw [hpident, ← mul_assoc]; exact degree_parameter_identity ht hb hD0
    have hi : 0 ≤ 1/(t:ℝ) := by positivity
    have hexp : (4*Real.exp 1)^(1-1/(t:ℝ)) ≤ 4*Real.exp 1 := by
      calc
        _ ≤ (4*Real.exp 1)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = _ := Real.rpow_one _
    have hm := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 4*(t:ℝ) by positivity)
    have hdiv := div_le_div_of_nonneg_right hm hD0.le
    have hlast : 4*(t:ℝ)*(4*Real.exp 1)/D Δ t b ≤ 1/8 := by
      apply (div_le_iff₀ hD0).mpr
      nlinarith
    calc
      _ ≤ 4*(t:ℝ)*fugacity Δ t b*((scale t b)^(1/(t:ℝ))*(cutoff Δ t b)^(1-1/(t:ℝ))) := by nlinarith [hh]
      _ = _ := heq
      _ ≤ _ := hdiv.trans hlast
  have hLam8 : fugacity Δ t b ≤ 1/8 := by
    have hh := fugacity_le_inv_D ht hb hD1
    have hD8 : 8 ≤ D Δ t b := (D_large_basic ht hDsmall).1
    have hi := (div_le_iff₀ hD0).mpr (show (1:ℝ) ≤ (1/8)*D Δ t b by linarith)
    exact hh.trans hi
  have hM : 0 ≤ cutoff Δ t b := (hs.le.trans (cutoff_ge_scale hb hD1))
  have hlast : (32/9)*Real.exp 1*D Δ t b ≤ p (fugacity Δ t b)*cutoff Δ t b := by
    have heq : p (fugacity Δ t b)*cutoff Δ t b =
        (4*Real.exp 1*D Δ t b)/(1+fugacity Δ t b) := by
      unfold p
      rw [div_mul_eq_mul_div, fugacity_cutoff ht hb hD0]
    rw [heq]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hLam8 (show 0 ≤ (32/9)*Real.exp 1*D Δ t b by positivity)]
  exact ⟨hfirst,hsecond,hlast⟩

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]


lemma two_sweep_exp (F : SimpleGraph V) [DecidableRel F.Adj] {lam : ℝ} (hlam : 0 < lam)
    (w₁ w₂ : List V) (h₁ : IsSweep Finset.univ w₁) (h₂ : IsSweep Finset.univ w₂) (I : State F) :
    let ν := push (point I) (word F lam (w₁++w₂))
    Real.exp (-lam*Fintype.card V) ≤ expectation ν (fun σ => if size σ.val = 0 then 1 else 0) ∧
    lam*Fintype.card V*Real.exp (-(avgDegree F+1)*lam) ≤ expectation ν (fun σ => size σ.val) := by
  have hh := LocalOccupancyIS.Glauber.lemma_9 F (avgDegree F) lam hlam le_rfl w₁ w₂ h₁ h₂ I
  have hp : 0 < 1+lam := by positivity
  have hlog : Real.log (1+lam) ≤ lam := by have h := Real.log_le_sub_one_of_pos hp; linarith
  constructor
  · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlog (neg_nonpos.mpr (Nat.cast_nonneg (Fintype.card V))))
    have heq : (1+lam)^(-(Fintype.card V:ℝ)) = Real.exp (Real.log (1+lam)*(-(Fintype.card V:ℝ))) := Real.rpow_def_of_pos hp _
    rw [← heq] at he
    have he' : Real.exp (-lam*Fintype.card V) ≤ (1+lam)^(-(Fintype.card V:ℝ)) := by
      convert he using 1 <;> congr 1 <;> ring
    exact he'.trans hh.1
  · have hd : 0 ≤ avgDegree F+1 := by linarith [avgDegree_nonneg F]
    have heq : p lam*Fintype.card V*(1+lam)^(-avgDegree F) =
        lam*Fintype.card V*Real.exp (-(avgDegree F+1)*Real.log (1+lam)) := by
      have hex : -(avgDegree F+1)*Real.log (1+lam) = Real.log (1+lam)*(-avgDegree F)+ -Real.log (1+lam) := by ring
      rw [hex,Real.exp_add,Real.exp_neg,Real.exp_log hp,Real.rpow_def_of_pos hp]
      unfold p
      ring
    have hex := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hd))
    have hm := mul_le_mul_of_nonneg_left hex (show 0 ≤ lam*Fintype.card V by positivity)
    rw [← heq] at hm
    exact hm.trans (hh.2.2.trans hh.2.1)

lemma score_linear (F : SimpleGraph V) [DecidableRel F.Adj] (ν : State F → ℝ) (lam β γ : ℝ) :
    expectation ν (fun σ => β*p lam*(if size σ.val = 0 then 1 else 0)+γ*size σ.val) =
      β*p lam*expectation ν (fun σ => if size σ.val = 0 then 1 else 0)+
        γ*expectation ν (fun σ => size σ.val) := by
  unfold expectation
  simp_rw [mul_add,Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intros <;> ring

lemma two_sweep_score (F : SimpleGraph V) [DecidableRel F.Adj] {Δ b : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hd : Density F t b) (hsmall : (Fintype.card V:ℝ) ≤ cutoff Δ t b)
    (z : ℝ) (hz : 0 ≤ z) (w₁ w₂ : List V) (h₁ : IsSweep Finset.univ w₁)
    (h₂ : IsSweep Finset.univ w₂) (I : State F) :
    1 ≤ expectation (push (point I) (word F (fugacity Δ t b) (w₁++w₂)))
      (fun σ => beta (fugacity Δ t b) z*p (fugacity Δ t b)*(if size σ.val = 0 then 1 else 0)+
        gamma (correction Δ t b) z*size σ.val) := by
  let lam := fugacity Δ t b
  let c := correction Δ t b
  have hlam : 0 < lam := fugacity_pos hb (D_large_basic ht hD).2.1
  have hc : 0 < c := (correction_bounds ht hD).1
  have hp : 0 < p lam := p_pos hlam
  have hz1 : 0 < 1+z := by linarith
  have hβ : 0 ≤ beta lam z := (div_pos (Real.exp_pos _) (mul_pos hp hz1)).le
  have hγ : 0 ≤ gamma c z := (one_div_pos.mpr (mul_pos hc hz1)).le
  have hh := two_sweep_exp F hlam w₁ w₂ h₁ h₂ I
  have hdeg : lam*(avgDegree F+1) ≤ 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b := by
    by_cases hzero : Fintype.card V = 0
    · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hzero
      have havg : avgDegree F = 0 := by simp [avgDegree]
      rw [havg,zero_add,mul_one]
      have hlamD := fugacity_le_inv_D ht hb (D_large_basic ht hD).2.2
      have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
      have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have ha : 0 ≤ 1-1/(t:ℝ) := by have hi := (div_le_one (by linarith : (0:ℝ) < t)).mpr ht'; linarith
      have hpw := Real.one_le_rpow (by linarith : 1 ≤ 4*Real.exp 1) ha
      have hnum : (1:ℝ) ≤ 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ)) := by nlinarith
      exact hlamD.trans (div_le_div_of_nonneg_right hnum (D_large_basic ht hD).2.1.le)
    · exact small_graph_degree_bound F ht hb hD (by omega) hd hsmall
  have hex : c ≤ Real.exp (-(avgDegree F+1)*lam) := by
    dsimp [c,correction]
    exact Real.exp_le_exp.mpr (by nlinarith [hdeg])
  have hE := (mul_le_mul_of_nonneg_left hex (show 0 ≤ lam*Fintype.card V by positivity)).trans hh.2
  have hS := add_le_add
    (mul_le_mul_of_nonneg_left hh.1 (mul_nonneg hβ hp.le))
    (mul_le_mul_of_nonneg_left hE hγ)
  rw [score_linear]
  have heq : beta lam z*p lam*Real.exp (-lam*Fintype.card V)+gamma c z*(lam*Fintype.card V*c) =
      (Real.exp (z-lam*Fintype.card V)+lam*Fintype.card V)/(1+z) := by
    unfold beta gamma
    simp only [neg_mul,Real.exp_neg,Real.exp_sub]
    field_simp [hp.ne',hc.ne',hz1.ne']
    <;> ring
  have hbase : 1 ≤ (Real.exp (z-lam*Fintype.card V)+lam*Fintype.card V)/(1+z) := by
    apply (le_div_iff₀ hz1).mpr
    have he := Real.add_one_le_exp (z-lam*Fintype.card V)
    linarith
  rw [heq] at hS
  exact hbase.trans hS

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma two_sweep_score_of_degree (F : SimpleGraph V) [DecidableRel F.Adj]
    {lam c a z : ℝ} (hlam : 0 < lam) (hc : 0 < c) (hcEq : c = Real.exp (-a)) (hz : 0 ≤ z)
    (hdeg : 1 ≤ Fintype.card V → lam*(avgDegree F+1) ≤ a)
    (w₁ w₂ : List V) (h₁ : IsSweep Finset.univ w₁) (h₂ : IsSweep Finset.univ w₂) (I : State F) :
    1 ≤ expectation (push (point I) (word F lam (w₁++w₂)))
      (fun σ => beta lam z*p lam*(if size σ.val = 0 then 1 else 0)+gamma c z*size σ.val) := by
  let ν := push (point I) (word F lam (w₁++w₂))
  have hν : MarkovMixing.IsDist ν := push_dist (point_dist I) (word_stochastic F hlam _)
  have hh := two_sweep_exp F hlam w₁ w₂ h₁ h₂ I
  have hE : c*(lam*Fintype.card V) ≤ expectation ν (fun σ => size σ.val) := by
    by_cases hzero : Fintype.card V = 0
    · simp only [hzero,Nat.cast_zero,mul_zero]
      exact expectation_nonneg hν (fun σ => Nat.cast_nonneg _)
    · have hcoef := hdeg (by omega)
      have hex : c ≤ Real.exp (-(avgDegree F+1)*lam) := by rw [hcEq]; exact Real.exp_le_exp.mpr (by nlinarith)
      have hm := mul_le_mul_of_nonneg_left hex (show 0 ≤ lam*Fintype.card V by positivity)
      have hle := hm.trans hh.2
      nlinarith
  have htangent := occupancy_tangent (Z := Real.exp (lam*Fintype.card V))
    hlam hc hz (Real.exp_pos _) (by simpa only [Real.log_exp] using hE)
  have hβ : 0 < beta lam z := div_pos (Real.exp_pos _) (mul_pos (p_pos hlam) (by linarith))
  have hP := mul_le_mul_of_nonneg_left hh.1 (mul_nonneg hβ.le (p_pos hlam).le)
  have heq : beta lam z*p lam/Real.exp (lam*Fintype.card V) = beta lam z*p lam*Real.exp (-lam*Fintype.card V) := by
    rw [neg_mul,Real.exp_neg]
    ring
  rw [heq] at htangent
  rw [score_linear]
  exact htangent.trans (add_le_add hP le_rfl)

lemma two_sweep_score_of_degree_dist (F : SimpleGraph V) [DecidableRel F.Adj]
    {lam c a z : ℝ} (hlam : 0 < lam) (hc : 0 < c) (hcEq : c = Real.exp (-a)) (hz : 0 ≤ z)
    (hdeg : 1 ≤ Fintype.card V → lam*(avgDegree F+1) ≤ a)
    (w₁ w₂ : List V) (h₁ : IsSweep Finset.univ w₁) (h₂ : IsSweep Finset.univ w₂)
    (ν : State F → ℝ) (hν : MarkovMixing.IsDist ν) :
    1 ≤ expectation (push ν (word F lam (w₁++w₂)))
      (fun σ => beta lam z*p lam*(if size σ.val = 0 then 1 else 0)+gamma c z*size σ.val) := by
  rw [point_mixture_expectation]
  calc
    _ = ∑ I,ν I*1 := by simpa using hν.2.symm
    _ ≤ _ := Finset.sum_le_sum (fun I _ => mul_le_mul_of_nonneg_left
      (two_sweep_score_of_degree F hlam hc hcEq hz hdeg w₁ w₂ h₁ h₂ I) (hν.1 I))

lemma p_mono {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) : p x ≤ p y := by
  unfold p
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma two_sweep_score_dist (F : SimpleGraph V) [DecidableRel F.Adj] {Δ b : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hd : Density F t b) (hsmall : (Fintype.card V:ℝ) ≤ cutoff Δ t b)
    (z : ℝ) (hz : 0 ≤ z) (w₁ w₂ : List V) (h₁ : IsSweep Finset.univ w₁)
    (h₂ : IsSweep Finset.univ w₂) (ν : State F → ℝ) (hν : MarkovMixing.IsDist ν) :
    1 ≤ expectation (push ν (word F (fugacity Δ t b) (w₁++w₂)))
      (fun σ => beta (fugacity Δ t b) z*p (fugacity Δ t b)*(if size σ.val = 0 then 1 else 0)+
        gamma (correction Δ t b) z*size σ.val) := by
  rw [point_mixture_expectation]
  calc
    _ = ∑ I, ν I*1 := by simpa using hν.2.symm
    _ ≤ _ := Finset.sum_le_sum (fun I _ => mul_le_mul_of_nonneg_left
      (two_sweep_score F ht hb hD hd hsmall z hz w₁ w₂ h₁ h₂ I) (hν.1 I))

lemma three_sweep_large_mean (F : SimpleGraph V) [DecidableRel F.Adj] {Δ b : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 1000*Real.exp 1*t ≤ D Δ t b)
    (hk : 1 ≤ Fintype.card V) (hd : Density F t b) (hlarge : cutoff Δ t b ≤ (Fintype.card V:ℝ))
    (w₁ w₂ w₃ : List V) (h₁ : IsSweep Finset.univ w₁) (h₂ : IsSweep Finset.univ w₂)
    (h₃ : IsSweep Finset.univ w₃) (I : State F) :
    2*D Δ t b ≤ (expectation (push (point I) (word F (fugacity Δ t b) (w₁++w₂))) (fun σ => size σ.val)+
      expectation (push (point I) (word F (fugacity Δ t b) (w₁++w₂++w₃))) (fun σ => size σ.val))/2 := by
  let lam := fugacity Δ t b
  let s := scale t b
  let M := cutoff Δ t b
  let d := D Δ t b
  have hDsmall : 8*Real.exp 1*t ≤ d := by dsimp [d]; nlinarith [Real.exp_pos 1]
  have hd0 : 0 < d := (D_large_basic ht hDsmall).2.1
  have hd1 : 1 ≤ d := (D_large_basic ht hDsmall).2.2
  have hs : 0 < s := scale_pos t hb
  have hM : 0 < M := hs.trans_le (cutoff_ge_scale hb hd1)
  have hlam : 0 < lam := fugacity_pos hb hd0
  have hp : 0 < p lam := p_pos hlam
  have hh := LocalOccupancyIS.Glauber.lemma_11 F t ht b lam hb hlam hk hd w₁ w₂ w₃ h₁ h₂ h₃ I
  have hc := sweep_large_constants ht hb hD
  have hfirst : 8*t*s*p lam ≤ 1/8 := hc.1
  have hsecond : 4*t*p lam*s^(1/(t:ℝ))*M^(1-1/(t:ℝ)) ≤ 1/8 := hc.2.1
  have hlast : (32/9)*Real.exp 1*d ≤ p lam*M := hc.2.2
  have hi : 0 ≤ 1/(t:ℝ) := by positivity
  have ha : 1-1/(t:ℝ) ≤ 1 := by linarith
  have hq : 0 ≤ 4*(t:ℝ)*p lam*s^(1/(t:ℝ)) := by positivity
  have hmono := fraction_rpow_mono hM hlarge hq ha
  have hf : 0 ≤ p lam*(1-8*t*s*p lam)/2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hmono hf
  have hparam : 2*d ≤ p lam*M*(1-8*t*s*p lam)/(2*(1+4*t*p lam*s^(1/(t:ℝ))*M^(1-1/(t:ℝ)))) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hnum := mul_le_mul_of_nonneg_left (show 7/8 ≤ 1-8*t*s*p lam by linarith) (mul_nonneg hp.le hM.le)
    have hlow := mul_le_mul_of_nonneg_right hlast (by norm_num : (0:ℝ) ≤ 7/8)
    have he : 2 ≤ Real.exp 1 := by have h := Real.add_one_le_exp 1; linarith
    have heD := mul_le_mul_of_nonneg_right he hd0.le
    have hden := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 4*d by positivity)
    nlinarith
  have heq (k : ℝ) : p lam*(1-8*t*s*p lam)/2*(k/(1+(4*t*p lam*s^(1/(t:ℝ)))*k^(1-1/(t:ℝ)))) =
      p lam*k*(1-8*t*s*p lam)/(2*(1+4*t*p lam*s^(1/(t:ℝ))*k^(1-1/(t:ℝ)))) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [heq,heq] at hm
  exact (hparam.trans hm).trans hh

lemma three_sweep_score (F : SimpleGraph V) [DecidableRel F.Adj] {Δ b : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 1000*Real.exp 1*t ≤ D Δ t b) (hd : Density F t b)
    (z : ℝ) (hz : 0 ≤ z) (hzD : z ≤ D Δ t b) (w : List V) (hw : IsSweep Finset.univ w) (I : State F) :
    1 ≤ (expectation (push (point I) (word F (fugacity Δ t b) (w++w)))
      (fun σ => beta (fugacity Δ t b) z*p (fugacity Δ t b)*(if size σ.val = 0 then 1 else 0)+gamma (correction Δ t b) z*size σ.val)+
      expectation (push (point I) (word F (fugacity Δ t b) (w++w++w)))
      (fun σ => beta (fugacity Δ t b) z*p (fugacity Δ t b)*(if size σ.val = 0 then 1 else 0)+gamma (correction Δ t b) z*size σ.val))/2 := by
  have hDsmall : 8*Real.exp 1*t ≤ D Δ t b := by nlinarith [Real.exp_pos 1]
  have hlam := fugacity_pos hb (D_large_basic ht hDsmall).2.1
  by_cases hsmall : (Fintype.card V:ℝ) ≤ cutoff Δ t b
  · have h₂ := two_sweep_score F ht hb hDsmall hd hsmall z hz w w hw hw I
    have h₃ := two_sweep_score_dist F ht hb hDsmall hd hsmall z hz w w hw hw
      (push (point I) (word F (fugacity Δ t b) w)) (push_dist (point_dist I) (word_stochastic F hlam w))
    rw [push_push, ← word_append] at h₃
    have he : w++(w++w) = w++w++w := by simp
    rw [he] at h₃
    linarith
  · have hlarge := (lt_of_not_ge hsmall).le
    have hM : 0 < cutoff Δ t b := (scale_pos t hb).trans_le (cutoff_ge_scale hb (D_large_basic ht hDsmall).2.2)
    have hk : 1 ≤ Fintype.card V := by
      by_contra hn
      have hz0 : Fintype.card V = 0 := by omega
      simp only [hz0,Nat.cast_zero] at hlarge
      exact (not_le_of_gt hM) hlarge
    have hm := three_sweep_large_mean F ht hb hD hk hd hlarge w w w hw hw hw I
    let lam := fugacity Δ t b
    let c := correction Δ t b
    have hc := correction_bounds ht hDsmall
    have hz1 : 0 < 1+z := by linarith
    have hγ : 0 < gamma c z := one_div_pos.mpr (mul_pos hc.1 hz1)
    have hβ : 0 < beta lam z := div_pos (Real.exp_pos _) (mul_pos (p_pos hlam) hz1)
    have hγD : 1 ≤ gamma c z*(2*D Δ t b) := by
      unfold gamma
      rw [one_div_mul_eq_div]
      apply (le_div_iff₀ (mul_pos hc.1 hz1)).mpr
      have hh := mul_le_mul_of_nonneg_right hc.2.1 hz1.le
      have hD1 := (D_large_basic ht hDsmall).2.2
      nlinarith
    have hprob (v : List V) : 0 ≤ beta lam z*p lam*expectation
        (push (point I) (word F lam v)) (fun σ => if size σ.val = 0 then 1 else 0) := by
      apply mul_nonneg (mul_nonneg hβ.le (p_pos hlam).le)
      exact expectation_nonneg (push_dist (point_dist I) (word_stochastic F hlam v))
        (fun σ => by split_ifs <;> norm_num)
    rw [score_linear,score_linear]
    have hh := mul_le_mul_of_nonneg_left hm hγ.le
    have h₂ := hprob (w++w)
    have h₃ := hprob (w++w++w)
    nlinarith

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma three_sweep_large_mean_of_constants (F : SimpleGraph V) [DecidableRel F.Adj]
    (t : ℕ) (ht : 1 ≤ t) (b lam M d : ℝ) (hb : 0 ≤ b) (hlam : 0 < lam)
    (hk : 1 ≤ Fintype.card V) (hd : Density F t b) (hM : 0 < M) (hd0 : 0 < d)
    (hlarge : M ≤ (Fintype.card V:ℝ))
    (hfirst : 8*t*scale t b*p lam ≤ 1/8)
    (hsecond : 4*t*p lam*(scale t b)^(1/(t:ℝ))*M^(1-1/(t:ℝ)) ≤ 1/8)
    (hlast : (32/9)*Real.exp 1*d ≤ p lam*M)
    (w₁ w₂ w₃ : List V) (h₁ : IsSweep Finset.univ w₁) (h₂ : IsSweep Finset.univ w₂)
    (h₃ : IsSweep Finset.univ w₃) (I : State F) :
    2*d ≤ (expectation (push (point I) (word F lam (w₁++w₂))) (fun σ => size σ.val)+
      expectation (push (point I) (word F lam (w₁++w₂++w₃))) (fun σ => size σ.val))/2 := by
  let s := scale t b
  have hs : 0 < s := scale_pos t hb
  have hp : 0 < p lam := p_pos hlam
  have hh := LocalOccupancyIS.Glauber.lemma_11 F t ht b lam hb hlam hk hd w₁ w₂ w₃ h₁ h₂ h₃ I
  have hi : 0 ≤ 1/(t:ℝ) := by positivity
  have ha : 1-1/(t:ℝ) ≤ 1 := by linarith
  have hq : 0 ≤ 4*(t:ℝ)*p lam*s^(1/(t:ℝ)) := by positivity
  have hmono := fraction_rpow_mono hM hlarge hq ha
  have hf : 0 ≤ p lam*(1-8*t*s*p lam)/2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hmono hf
  have hparam : 2*d ≤ p lam*M*(1-8*t*s*p lam)/(2*(1+4*t*p lam*s^(1/(t:ℝ))*M^(1-1/(t:ℝ)))) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hnum := mul_le_mul_of_nonneg_left (show 7/8 ≤ 1-8*t*s*p lam by linarith) (mul_nonneg hp.le hM.le)
    have hlow := mul_le_mul_of_nonneg_right hlast (by norm_num : (0:ℝ) ≤ 7/8)
    have he : 2 ≤ Real.exp 1 := by have h := Real.add_one_le_exp 1; linarith
    have heD := mul_le_mul_of_nonneg_right he hd0.le
    have hden := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 4*d by positivity)
    nlinarith
  have heq (k : ℝ) : p lam*(1-8*t*s*p lam)/2*(k/(1+(4*t*p lam*s^(1/(t:ℝ)))*k^(1-1/(t:ℝ)))) =
      p lam*k*(1-8*t*s*p lam)/(2*(1+4*t*p lam*s^(1/(t:ℝ))*k^(1-1/(t:ℝ)))) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [heq,heq] at hm
  exact (hparam.trans hm).trans hh

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma dynamic_three_sweep_score (F : SimpleGraph V) [DecidableRel F.Adj] {Δ b lam : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 1000*Real.exp 1*t ≤ D Δ t b) (hd : Density F t b)
    (hlam : 0 < lam) (hLam : lam ≤ fugacity Δ t b)
    (hlargep : (32/9)*Real.exp 1*D Δ t b ≤ p lam*cutoff Δ t b)
    (z : ℝ) (hz : 0 ≤ z) (hzD : z ≤ D Δ t b) (w : List V) (hw : IsSweep Finset.univ w) (I : State F) :
    1 ≤ (expectation (push (point I) (word F lam (w++w)))
      (fun σ => beta lam z*p lam*(if size σ.val = 0 then 1 else 0)+gamma (correction Δ t b) z*size σ.val)+
      expectation (push (point I) (word F lam (w++w++w)))
      (fun σ => beta lam z*p lam*(if size σ.val = 0 then 1 else 0)+gamma (correction Δ t b) z*size σ.val))/2 := by
  have hDsmall : 8*Real.exp 1*t ≤ D Δ t b := by nlinarith [Real.exp_pos 1]
  have hsrcLam := fugacity_pos hb (D_large_basic ht hDsmall).2.1
  have hc := correction_bounds ht hDsmall
  have hcoef (hk : 1 ≤ Fintype.card V) (hsmall : (Fintype.card V:ℝ) ≤ cutoff Δ t b) :
      lam*(avgDegree F+1) ≤ 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b := by
    have hh := mul_le_mul_of_nonneg_right hLam (show 0 ≤ avgDegree F+1 by linarith [avgDegree_nonneg F])
    exact hh.trans (small_graph_degree_bound F ht hb hDsmall hk hd hsmall)
  by_cases hsmall : (Fintype.card V:ℝ) ≤ cutoff Δ t b
  · have h₂ := two_sweep_score_of_degree F hlam hc.1 rfl hz (fun hk => hcoef hk hsmall) w w hw hw I
    have h₃ := two_sweep_score_of_degree_dist F hlam hc.1 rfl hz (fun hk => hcoef hk hsmall) w w hw hw
      (push (point I) (word F lam w)) (push_dist (point_dist I) (word_stochastic F hlam w))
    rw [push_push,← word_append] at h₃
    have he : w++(w++w) = w++w++w := by simp
    rw [he] at h₃
    linarith
  · have hlarge := (lt_of_not_ge hsmall).le
    have hM : 0 < cutoff Δ t b := (scale_pos t hb).trans_le (cutoff_ge_scale hb (D_large_basic ht hDsmall).2.2)
    have hk : 1 ≤ Fintype.card V := by
      by_contra hn
      have hzero : Fintype.card V = 0 := by omega
      simp only [hzero,Nat.cast_zero] at hlarge
      exact (not_le_of_gt hM) hlarge
    have hpm := p_mono hlam hsrcLam hLam
    have hs := scale_pos t hb
    have hconstants := sweep_large_constants ht hb hD
    have hfirst : 8*t*scale t b*p lam ≤ 1/8 := by
      have hh := mul_le_mul_of_nonneg_left hpm (show 0 ≤ 8*(t:ℝ)*scale t b by positivity)
      nlinarith [hconstants.1]
    have hsecond : 4*t*p lam*(scale t b)^(1/(t:ℝ))*(cutoff Δ t b)^(1-1/(t:ℝ)) ≤ 1/8 := by
      have hh := mul_le_mul_of_nonneg_right hpm
        (show 0 ≤ 4*(t:ℝ)*(scale t b)^(1/(t:ℝ))*(cutoff Δ t b)^(1-1/(t:ℝ)) by positivity)
      nlinarith [hconstants.2.1]
    have hm := three_sweep_large_mean_of_constants F t ht b lam (cutoff Δ t b) (D Δ t b) hb hlam hk hd
      hM (D_large_basic ht hDsmall).2.1 hlarge hfirst hsecond hlargep w w w hw hw hw I
    let c := correction Δ t b
    have hz1 : 0 < 1+z := by linarith
    have hγ : 0 < gamma c z := one_div_pos.mpr (mul_pos hc.1 hz1)
    have hβ : 0 < beta lam z := div_pos (Real.exp_pos _) (mul_pos (p_pos hlam) hz1)
    have hγD : 1 ≤ gamma c z*(2*D Δ t b) := by
      unfold gamma
      rw [one_div_mul_eq_div]
      apply (le_div_iff₀ (mul_pos hc.1 hz1)).mpr
      have hh := mul_le_mul_of_nonneg_right hc.2.1 hz1.le
      have hD1 := (D_large_basic ht hDsmall).2.2
      nlinarith
    have hprob (v : List V) : 0 ≤ beta lam z*p lam*expectation
        (push (point I) (word F lam v)) (fun σ => if size σ.val = 0 then 1 else 0) := by
      apply mul_nonneg (mul_nonneg hβ.le (p_pos hlam).le)
      exact expectation_nonneg (push_dist (point_dist I) (word_stochastic F hlam v))
        (fun σ => by split_ifs <;> norm_num)
    rw [score_linear,score_linear]
    have hh := mul_le_mul_of_nonneg_left hm hγ.le
    have h₂ := hprob (w++w)
    have h₃ := hprob (w++w++w)
    nlinarith

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

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma rounded_fugacity_bounds {Δ b q : ℝ} {t : ℕ} (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hqlo : scale t b*D Δ t b^(2*t-1) ≤ q) (hqhi : q ≤ scale t b*D Δ t b^(2*t-1)+2) :
    0 < 1/q ∧ 1/q ≤ fugacity Δ t b ∧
    fugacity Δ t b/(1+2*fugacity Δ t b) ≤ 1/q ∧
    |(1/q)/fugacity Δ t b-1| ≤ 2/D Δ t b ∧
    fugacity Δ t b/(1+3*fugacity Δ t b) ≤ p (1/q) := by
  let x := scale t b*D Δ t b^(2*t-1)
  let lam := fugacity Δ t b
  have hd := (D_large_basic ht hD).2.1
  have hx : 0 < x := by dsimp [x]; exact mul_pos (scale_pos t hb) (pow_pos hd _)
  have hq : 0 < q := hx.trans_le hqlo
  have hlam : 0 < lam := fugacity_pos hb hd
  have hlameq : lam = 1/x := rfl
  have hhat : 1/q ≤ lam := div_le_div_of_nonneg_left (by norm_num) hx hqlo
  have hlo : lam/(1+2*lam) ≤ 1/q := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hq hqhi
    have heq : lam/(1+2*lam) = 1/(x+2) := by rw [hlameq]; field_simp <;> ring
    rw [heq]
    exact hh
  have hratio : (1/q)/lam = x/q := by rw [hlameq]; field_simp
  have hratio1 : x/q ≤ 1 := (div_le_one hq).mpr hqlo
  have herror : |(1/q)/lam-1| ≤ 2/D Δ t b := by
    rw [hratio,abs_of_nonpos (sub_nonpos.mpr hratio1)]
    have heq : -(x/q-1) = (q-x)/q := by field_simp <;> ring
    rw [heq]
    calc
      _ ≤ 2/q := div_le_div_of_nonneg_right (by linarith) hq.le
      _ ≤ 2/x := div_le_div_of_nonneg_left (by norm_num) hx hqlo
      _ = 2*lam := by rw [hlameq]; ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (fugacity_le_inv_D ht hb (D_large_basic ht hD).2.2) (by norm_num : (0:ℝ) ≤ 2)
        change 2*lam ≤ _
        simpa only [mul_one_div] using hh
  have hp : lam/(1+3*lam) ≤ p (1/q) := by
    have heq : lam/(1+3*lam) = 1/(x+3) := by rw [hlameq]; field_simp <;> ring
    have hpq : p (1/q) = 1/(q+1) := by unfold p; field_simp <;> ring
    rw [heq,hpq]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith : 0 < q+1) (by linarith)
  exact ⟨one_div_pos.mpr hq,hhat,hlo,herror,hp⟩

lemma rounded_sweep_constants {Δ b q : ℝ} {t : ℕ} (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 1000*Real.exp 1*t ≤ D Δ t b)
    (hqlo : scale t b*D Δ t b^(2*t-1) ≤ q) (hqhi : q ≤ scale t b*D Δ t b^(2*t-1)+2) :
    8*t*scale t b*p (1/q) ≤ 1/8 ∧
    4*t*p (1/q)*(scale t b)^(1/(t:ℝ))*(cutoff Δ t b)^(1-1/(t:ℝ)) ≤ 1/8 ∧
    (32/9)*Real.exp 1*D Δ t b ≤ p (1/q)*cutoff Δ t b := by
  have hDsmall : 8*Real.exp 1*t ≤ D Δ t b := by nlinarith [Real.exp_pos 1]
  have hD0 := (D_large_basic ht hDsmall).2.1
  have hD1 := (D_large_basic ht hDsmall).2.2
  have hround := rounded_fugacity_bounds ht hb hDsmall hqlo hqhi
  have hlam := fugacity_pos hb hD0
  have hhatpos := hround.1
  have hs := scale_pos t hb
  have hpLam : p (1/q) ≤ p (fugacity Δ t b) := by
    unfold p
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [hround.2.1]
  have hc := sweep_large_constants ht hb hD
  have hM : 0 < cutoff Δ t b := (scale_pos t hb).trans_le (cutoff_ge_scale hb hD1)
  have hLam24 : fugacity Δ t b ≤ 1/24 := by
    have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hd24 : 24 ≤ D Δ t b := by nlinarith
    have hi := (div_le_iff₀ hD0).mpr (show (1:ℝ) ≤ (1/24)*D Δ t b by linarith)
    exact (fugacity_le_inv_D ht hb hD1).trans hi
  refine ⟨?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hpLam (show 0 ≤ 8*(t:ℝ)*scale t b by positivity)
    nlinarith [hc.1]
  · have hh := mul_le_mul_of_nonneg_right hpLam
      (show 0 ≤ 4*(t:ℝ)*(scale t b)^(1/(t:ℝ))*(cutoff Δ t b)^(1-1/(t:ℝ)) by positivity)
    nlinarith [hc.2.1]
  · have hm := mul_le_mul_of_nonneg_right hround.2.2.2.2 hM.le
    have heq : (fugacity Δ t b/(1+3*fugacity Δ t b))*cutoff Δ t b =
        4*Real.exp 1*D Δ t b/(1+3*fugacity Δ t b) := by rw [div_mul_eq_mul_div,fugacity_cutoff ht hb hD0]
    rw [heq] at hm
    apply le_trans _ hm
    apply (le_div_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hLam24 (show 0 ≤ (32/9)*Real.exp 1*D Δ t b by positivity)
    nlinarith

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma lambert_mono {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
    RiskBalancingMNL.lambertW x ≤ RiskBalancingMNL.lambertW y := by
  have hxf := lambert_facts hx
  have hyf := lambert_facts hy
  by_contra hn
  have hh := mul_exp_strictMonoOn hyf.1 hxf.1 (lt_of_not_ge hn)
  dsimp only at hh
  rw [hxf.2,hyf.2] at hh
  linarith

lemma optimizer_bounds_of_le {Δ b lam : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) (hlam : 0 < lam) (hLam : lam ≤ fugacity Δ t b) :
    0 < optimizer Δ lam (correction Δ t b) ∧ optimizer Δ lam (correction Δ t b) < D Δ t b := by
  have hΔ0 : 0 < Δ := by linarith
  have hsrc := fugacity_pos hb (D_large_basic ht hD).2.1
  have hc := (correction_bounds ht hD).1
  have hpos : 0 < p lam*Δ/correction Δ t b := div_pos (mul_pos (p_pos hlam) hΔ0) hc
  have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (p_mono hlam hsrc hLam) hΔ0.le) hc.le
  have hspos : 0 ≤ p (fugacity Δ t b)*Δ/correction Δ t b := (div_pos (mul_pos (p_pos hsrc) hΔ0) hc).le
  have hopt := lambert_mono hpos.le hspos hm
  exact ⟨lambert_pos hpos,hopt.trans_lt (optimizer_bounds hΔ ht hb hD).2⟩

lemma optimizer_lower_of_rounded {Δ b lam : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) (hlam : 0 < lam) (hLam : lam ≤ fugacity Δ t b)
    (hpLower : fugacity Δ t b/(1+3*fugacity Δ t b) ≤ p lam) :
    D Δ t b-3*(t:ℝ)*Real.log (D Δ t b) ≤ optimizer Δ lam (correction Δ t b) := by
  let d := D Δ t b
  let l := fugacity Δ t b
  let c := correction Δ t b
  let z := optimizer Δ lam c
  have hd : 0 < d := (D_large_basic ht hD).2.1
  have hd8 : 8 ≤ d := (D_large_basic ht hD).1
  have hl : 0 < l := fugacity_pos hb hd
  have hc := correction_bounds ht hD
  have hΔ0 : 0 < Δ := by linarith
  have hz := optimizer_bounds_of_le hΔ ht hb hD hlam hLam
  have hp := p_pos hlam
  have hx : 0 < p lam*Δ/c := div_pos (mul_pos hp hΔ0) hc.1
  have hlower : l*Δ/(1+3*l) ≤ p lam*Δ/c := by
    have hh := mul_le_mul_of_nonneg_right hpLower hΔ0.le
    have hh' : l*Δ/(1+3*l) ≤ p lam*Δ := by convert hh using 1 <;> first | rfl | ring
    have hself : p lam*Δ ≤ p lam*Δ/c := by
      apply (le_div_iff₀ hc.1).mpr
      exact mul_le_of_le_one_right (mul_nonneg hp.le hΔ0.le) hc.2.1
    exact hh'.trans hself
  have hlog := Real.log_le_log (div_pos (mul_pos hl hΔ0) (by positivity)) hlower
  have he := (lambert_facts hx.le).2
  change z*Real.exp z = p lam*Δ/c at he
  have heLog := congrArg Real.log he
  rw [Real.log_mul hz.1.ne' (Real.exp_pos z).ne',Real.log_exp] at heLog
  have hlogval : Real.log (l*Δ/(1+3*l)) = d-((2*t-1:ℕ):ℝ)*Real.log d-Real.log (1+3*l) := by
    change Real.log (fugacity Δ t b*Δ/(1+3*l)) = _
    rw [fugacity_degree hΔ0 hb,Real.log_div (div_pos (Real.exp_pos _) (pow_pos hd _)).ne' (by positivity),
      Real.log_div (Real.exp_pos _).ne' (pow_pos hd _).ne',Real.log_exp,Real.log_pow]
  rw [hlogval,← heLog] at hlog
  have hlogz : Real.log z ≤ Real.log d := Real.log_le_log hz.1 hz.2.le
  have hlog1 : Real.log (1+3*l) ≤ 1 := by
    have hll := fugacity_le_inv_D ht hb (D_large_basic ht hD).2.2
    have h3 : 3/d ≤ 1 := (div_le_one hd).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_left hll (by norm_num : (0:ℝ) ≤ 3)
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1+3*l by positivity)
    change l ≤ 1/d at hll
    change 3*l ≤ 3*(1/d) at hm
    have hm' : 3*l ≤ 3/d := by convert hm using 1 <;> ring
    linarith
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hlogd := log_D_one_le ht hD
  have htl : 1 ≤ (t:ℝ)*Real.log d := by nlinarith
  have hr : ((2*t-1:ℕ):ℝ) = 2*(t:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ 2*t)]; norm_num
  rw [hr] at hlog
  change d-3*(t:ℝ)*Real.log d ≤ z
  nlinarith

lemma gamma_error_of_lower {Δ b lam : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) (hlam : 0 < lam)
    (hbounds : 0 < optimizer Δ lam (correction Δ t b) ∧ optimizer Δ lam (correction Δ t b) ≤ D Δ t b)
    (hlower : D Δ t b-3*(t:ℝ)*Real.log (D Δ t b) ≤ optimizer Δ lam (correction Δ t b))
    (hsmall : relativeError Δ t b ≤ 1/(4*(16*Real.exp 1+3))) :
    |Gamma Δ lam (correction Δ t b)*D Δ t b/Δ-1| ≤ (4*(16*Real.exp 1+3))*relativeError Δ t b := by
  let d := D Δ t b
  let z := optimizer Δ (lam) (correction Δ t b)
  let c := correction Δ t b
  let a := 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/d
  let e := relativeError Δ t b
  let C := 16*Real.exp 1+3
  let E := C*e
  have hd : 0 < d := (D_large_basic ht hD).2.1
  have hz : 0 < z := hbounds.1
  have hzd : z ≤ d := hbounds.2
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
    have hh := hlower
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
  have hGam := gamma_optimizer_identity hΔ0 hlam hc
  have hEq : Gamma Δ (lam) (correction Δ t b)*D Δ t b/Δ = d/(c*z) := by
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

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma dynamic_three_sweep_point_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) {t : ℕ} (ht : 1 ≤ t) {b lam : ℝ} (hb : 0 ≤ b)
    (hd : HereditaryDensity G t b) (hD : 1000*Real.exp 1*t ≤ D Δ t b)
    (hlam : 0 < lam) (hLam : lam ≤ fugacity Δ t b)
    (hlargep : (32/9)*Real.exp 1*D Δ t b ≤ p lam*cutoff Δ t b)
    (w : V → List V) (hw : ∀ u, IsSweep (G.neighborFinset u) (w u)) (I : State G) (u : V) :
    1 ≤ (expectation (push (point I) (word G lam (w u++w u)))
      (score G lam (beta lam (optimizer Δ lam (correction Δ t b)))
        (gamma (correction Δ t b) (optimizer Δ lam (correction Δ t b))) u)+
      expectation (push (point I) (word G lam (w u++w u++w u)))
      (score G lam (beta lam (optimizer Δ lam (correction Δ t b)))
        (gamma (correction Δ t b) (optimizer Δ lam (correction Δ t b))) u))/2 := by
  classical
  let A := available G u I
  let F := G.induce (↑A : Set V)
  let ww := restrictWord A (w u)
  let z := optimizer Δ lam (correction Δ t b)
  have hDsmall : 8*Real.exp 1*t ≤ D Δ t b := by nlinarith [Real.exp_pos 1]
  have hz := optimizer_bounds_of_le (show (1:ℝ) ≤ Δ by exact_mod_cast hΔ) ht hb hDsmall hlam hLam
  have hF : Density F t b := hd u A (available_subset G u I)
  have hww : IsSweep Finset.univ ww := restrictWord_sweep (available_subset G u I) (w u) (hw u)
  have hword : ∀ v ∈ w u, v ∈ G.neighborFinset u := by
    intro v hv
    rw [← (hw u).2]
    simpa using hv
  have htwo : ∀ v ∈ w u++w u, v ∈ G.neighborFinset u := by simpa only [List.mem_append,or_self] using hword
  have hthree : ∀ v ∈ w u++w u++w u, v ∈ G.neighborFinset u := by simpa only [List.mem_append,or_self] using hword
  rw [available_score_transport G hlam _ _ u I _ htwo, available_score_transport G hlam _ _ u I _ hthree]
  have he₂ : restrictWord A (w u++w u) = ww++ww := List.filterMap_append
  have he₃ : restrictWord A (w u++w u++w u) = ww++ww++ww := by simp only [restrictWord,List.filterMap_append]; rfl
  change 1 ≤ (_+_)/2
  rw [show restrictWord (available G u I) (w u++w u) = ww++ww from he₂,
    show restrictWord (available G u I) (w u++w u++w u) = ww++ww++ww from he₃]
  exact dynamic_three_sweep_score F ht hb hD hF hlam hLam hlargep z hz.1.le hz.2.le ww hww (restrictInitial G u I)

lemma dynamic_prefix_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) {t : ℕ} (ht : 1 ≤ t) {b lam : ℝ} (hb : 0 ≤ b)
    (hd : HereditaryDensity G t b) (hD : 1000*Real.exp 1*t ≤ D Δ t b)
    (hlam : 0 < lam) (hLam : lam ≤ fugacity Δ t b)
    (hlargep : (32/9)*Real.exp 1*D Δ t b ≤ p lam*cutoff Δ t b)
    (w : V → List V) (hw : ∀ u, IsSweep (G.neighborFinset u) (w u)) :
    PrefixCertificate G lam
      (beta lam (optimizer Δ lam (correction Δ t b)))
      (gamma (correction Δ t b) (optimizer Δ lam (correction Δ t b)))
      0 (threeWords w) (threePrefixes w) := by
  intro ν hν u
  simp only [sub_zero,threePrefixes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero]
  have he₂ : (threeWords w u).take (2*(w u).length) = w u++w u := by
    unfold threeWords
    have he : 2*(w u).length = (w u++w u).length := by simp; omega
    rw [he,List.take_left]
  have he₃ : (threeWords w u).take (3*(w u).length) = w u++w u++w u := by
    unfold threeWords
    have he : 3*(w u).length = (w u++w u++w u).length := by simp; omega
    rw [he,List.take_length]
  rw [he₂,he₃,point_mixture_expectation,point_mixture_expectation]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun I _ =>
    mul_le_mul_of_nonneg_left (dynamic_three_sweep_point_certificate G hΔ ht hb hd hD hlam hLam hlargep w hw I u) (hν.1 I))
  simp only [mul_one,hν.2] at hh
  simp only [mul_div,mul_add,← Finset.sum_div,Finset.sum_add_distrib] at hh
  norm_num at hh ⊢
  exact hh

lemma dynamic_finite_conclusion [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hbound : DegreeBound G Δ) {t : ℕ} (ht : 1 ≤ t) {b lam : ℝ} (hb : 0 ≤ b)
    (hd : HereditaryDensity G t b) (hD : 1000*Real.exp 1*t ≤ D Δ t b)
    (hlam : 0 < lam) (hLam : lam ≤ fugacity Δ t b)
    (hlargep : (32/9)*Real.exp 1*D Δ t b ≤ p lam*cutoff Δ t b)
    (w : V → List V) (hw : ∀ u, IsSweep (G.neighborFinset u) (w u)) :
    FiniteConclusion G Δ lam (correction Δ t b) w := by
  have hDsmall : 8*Real.exp 1*t ≤ D Δ t b := by nlinarith [Real.exp_pos 1]
  exact finite_from_certificate G hbound hlam
    (correction_bounds ht hDsmall).1 w hw (dynamic_prefix_certificate G hΔ ht hb hd hD hlam hLam hlargep w hw)

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma rounded_finite {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Δ t : ℕ} {b q : ℝ}
    (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b) (hbound : DegreeBound G Δ)
    (hd : HereditaryDensity G t b) (hD : 1000*Real.exp 1*t ≤ D Δ t b)
    (hqlo : scale t b*D Δ t b^(2*t-1) ≤ q) (hqhi : q ≤ scale t b*D Δ t b^(2*t-1)+2)
    (hsmall : relativeError Δ t b ≤ 1/(4*(16*Real.exp 1+3)))
    (w : V → List V) (hw : ∀ u, IsSweep (G.neighborFinset u) (w u)) :
    |(1/q)/fugacity Δ t b-1| ≤ 2/D Δ t b ∧
    FiniteConclusion G Δ (1/q) (correction Δ t b) w ∧
    |Gamma Δ (1/q) (correction Δ t b)*D Δ t b/Δ-1| ≤
      (4*(16*Real.exp 1+3))*relativeError Δ t b := by
  have hDsmall : 8*Real.exp 1*t ≤ D Δ t b := by nlinarith [Real.exp_pos 1]
  have hf := rounded_fugacity_bounds ht hb hDsmall hqlo hqhi
  have hc := rounded_sweep_constants ht hb hD hqlo hqhi
  have hopt := optimizer_bounds_of_le (show (1:ℝ) ≤ Δ by exact_mod_cast hΔ) ht hb hDsmall hf.1 hf.2.1
  have hlower := optimizer_lower_of_rounded (show (1:ℝ) ≤ Δ by exact_mod_cast hΔ) ht hb hDsmall hf.1 hf.2.1 hf.2.2.2.2
  refine ⟨hf.2.2.2.1,dynamic_finite_conclusion G hΔ hbound ht hb hd hD hf.1 hf.2.1 hc.2.2 w hw,?_⟩
  exact gamma_error_of_lower (show (1:ℝ) ≤ Δ by exact_mod_cast hΔ) ht hDsmall hf.1 ⟨hopt.1,hopt.2.le⟩ hlower hsmall

end
end LocalOccupancyIS.Glauber

open LocalOccupancyIS.Glauber

theorem solution (n Δ t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (b q : ℝ)
    (hn : 0 < n) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b) (hbound : DegreeBound G Δ)
    (hd : HereditaryDensity G t b) (hD : 1000*Real.exp 1*t ≤ D Δ t b)
    (hqlo : scale t b*D Δ t b^(2*t-1) ≤ q) (hqhi : q ≤ scale t b*D Δ t b^(2*t-1)+2)
    (hsmall : relativeError Δ t b ≤ 1/(4*(16*Real.exp 1+3)))
    (w : Fin n → List (Fin n)) (hw : ∀ u, IsSweep (G.neighborFinset u) (w u)) :
    |(1/q)/fugacity Δ t b-1| ≤ 2/D Δ t b ∧
    FiniteConclusion G Δ (1/q) (correction Δ t b) w ∧
    |Gamma Δ (1/q) (correction Δ t b)*D Δ t b/Δ-1| ≤
      (4*(16*Real.exp 1+3))*relativeError Δ t b := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  exact rounded_finite G hΔ ht hb hbound hd hD hqlo hqhi hsmall w hw
