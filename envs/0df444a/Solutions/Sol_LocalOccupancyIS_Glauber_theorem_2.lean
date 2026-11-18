-- Prove2me | solution 1 for LocalOccupancyIS.Glauber.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:19:57.813882+00:00
-- url     : https://prove2.me/submissions/4d32a1f3-d6da-4b4d-80e4-cd66f24971c1

import Definitions.Def_LocalOccupancyIS_Glauber_Dynamics
import Theorems.Thm_SinkhornHall_lemma_1_1
import Definitions.Def_LocalOccupancyIS_Glauber_Parameters
import Definitions.Def_LocalOccupancyIS_Glauber_Execution
import Theorems.Thm_LocalOccupancyIS_Glauber_lemma_7

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

open LocalOccupancyIS.Glauber
open scoped BigOperators

theorem solution {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : DegreeBound G Δ)
    (lam β γ η : ℝ) (hlam : 0 < lam) (hβ : 0 < β) (hγ : 0 < γ)
    (hη : 0 ≤ η ∧ η < 1) (w : V → List V) (hw : NeighborhoodWords G w)
    (hc : WordCertificate G lam β γ η w ∨
      ∃ a : V → List ℕ, Prefixes w a ∧ PrefixCertificate G lam β γ η w a)
    (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) :
    let H₀ := kl ν (HardCoreBochner.hcLaw G lam)
    let Hlam := entropyBound (Fintype.card V) lam
    let Γ := β + γ * Δ
    let C := transferConstant Δ (occurrences w) lam β γ
    MarkovMixing.IsStochastic (K G lam) ∧
    K G lam = (Fintype.card V : ℝ)⁻¹ • ∑ u, P G lam u ∧
    H₀ ≤ Hlam ∧
    ∀ T : ℕ, 1 ≤ T →
      timeMean G lam ν T ≥ Fintype.card V / Γ * (1 - η - C * Real.sqrt (H₀ / (2*T))) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → C^2 * Hlam / (2*ε^2) ≤ T →
        timeMean G lam ν T ≥ (1-η-ε)*Fintype.card V/Γ := by
  refine ⟨scan_stochastic G hlam, scan_eq G lam, initial_entropy_bound G hlam hν, ?_⟩
  intro T hT
  refine ⟨transfer_time_bound G hΔ hlam hβ hγ w hc hν T hT, ?_⟩
  intro ε hε hε1 hhor
  exact transfer_finite_bound G hΔ hlam hβ hγ w hc hν T hT hε hhor
