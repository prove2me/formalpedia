-- Prove2me | solution 1 for LocalOccupancyIS.Glauber.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:30:44.743275+00:00
-- url     : https://prove2.me/submissions/82b4ae23-e3f6-4b41-acf4-00f612cdf2aa

import Definitions.Def_LocalOccupancyIS_Glauber_Dynamics
import Theorems.Thm_SinkhornHall_lemma_1_1
import Definitions.Def_LocalOccupancyIS_Glauber_Parameters
import Definitions.Def_LocalOccupancyIS_Glauber_Execution
import Theorems.Thm_LocalOccupancyIS_Glauber_lemma_5

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
open LocalOccupancyIS.Glauber

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (t : ℕ) (ht : 1 ≤ t)
    (b lam : ℝ) (hb : 0 ≤ b) (hlam : 0 < lam)
    (hk : 1 ≤ Fintype.card V) (hd : Density F t b)
    (w₁ w₂ w₃ : List V) (h₁ : IsSweep Finset.univ w₁)
    (h₂ : IsSweep Finset.univ w₂) (h₃ : IsSweep Finset.univ w₃) (I : State F) :
    let X := push (point I) (word F lam (w₁ ++ w₂))
    let Y := push (point I) (word F lam (w₁ ++ w₂ ++ w₃))
    (expectation X (fun σ => size σ.val) + expectation Y (fun σ => size σ.val)) / 2 ≥
      p lam * Fintype.card V * (1 - 8*t*scale t b*p lam) /
        (2*(1+4*t*p lam*(scale t b)^(1/(t:ℝ))*(Fintype.card V : ℝ)^(1-1/(t:ℝ)))) := by
  classical
  dsimp only
  simp only [word_append, ← push_push]
  let ν₁ := push (point I) (word F lam w₁)
  let X := push ν₁ (word F lam w₂)
  let Y := push X (word F lam w₃)
  let x (v : V) := expectation X (fun σ => if σ.val v = true then (1:ℝ) else 0)
  let y (v : V) := expectation Y (fun σ => if σ.val v = true then (1:ℝ) else 0)
  let EX := expectation X (fun σ => size σ.val)
  let EY := expectation Y (fun σ => size σ.val)
  let s := scale t b
  let K : ℝ := Fintype.card V
  let c := 4*t*s^(1/(t:ℝ))*K^(1-1/(t:ℝ))
  have hν₁ : MarkovMixing.IsDist ν₁ := push_dist (point_dist I) (word_stochastic F hlam w₁)
  have hX : MarkovMixing.IsDist X := push_dist hν₁ (word_stochastic F hlam w₂)
  have hY : MarkovMixing.IsDist Y := push_dist hX (word_stochastic F hlam w₃)
  have hx (v : V) : 0 ≤ x v ∧ x v ≤ p lam := sweep_marginal_range F hlam ν₁ hν₁ w₂ h₂ v
  have hy (v : V) : 0 ≤ y v ∧ y v ≤ p lam := sweep_marginal_range F hlam X hX w₃ h₃ v
  have hsx : (∑ v, x v) = EX := (expectation_size_sum F X).symm
  have hsy : (∑ v, y v) = EY := (expectation_size_sum F Y).symm
  have hbX := (LocalOccupancyIS.Glauber.lemma_5 F t ht b hb hk hd (p lam) x hx).1
  have hbY := (LocalOccupancyIS.Glauber.lemma_5 F t ht b hb hk hd (p lam) y hy).1
  change (∑ v, (F.degree v : ℝ)*x v) ≤ 4*t*s*p lam*K + c*(∑ v, x v) at hbX
  change (∑ v, (F.degree v : ℝ)*y v) ≤ 4*t*s*p lam*K + c*(∑ v, y v) at hbY
  rw [hsx] at hbX
  rw [hsy] at hbY
  have hu := sweep_union_bound F hlam X hX w₃ h₃
  change p lam*K - p lam * (∑ v, (F.degree v : ℝ)*(x v+y v)) ≤ EY at hu
  simp_rw [mul_add, Finset.sum_add_distrib] at hu
  have hweighted := mul_le_mul_of_nonneg_left (add_le_add hbX hbY) (p_pos hlam).le
  have hEX : 0 ≤ EX := expectation_nonneg hX (fun σ => Nat.cast_nonneg _)
  have hs : 0 < s := by
    dsimp [s, scale]
    exact Real.rpow_pos_of_pos (by linarith) _
  have hc : 0 ≤ c := by
    dsimp [c, K]
    positivity
  have hp := p_pos hlam
  have hden : 0 < 2*(1+p lam*c) := by positivity
  change (EX+EY)/2 ≥ p lam*K*(1-8*t*s*p lam) /
    (2*(1+4*t*p lam*s^(1/(t:ℝ))*K^(1-1/(t:ℝ))))
  have hdeneq : 4*(t:ℝ)*p lam*s^(1/(t:ℝ))*K^(1-1/(t:ℝ)) = p lam*c := by dsimp [c]; ring
  rw [hdeneq]
  apply (div_le_iff₀ hden).mpr
  nlinarith
