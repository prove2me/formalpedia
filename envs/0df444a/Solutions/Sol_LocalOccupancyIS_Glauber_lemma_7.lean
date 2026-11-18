-- Prove2me | solution 1 for LocalOccupancyIS.Glauber.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:05:26.858884+00:00
-- url     : https://prove2.me/submissions/9896df84-32ab-47db-889e-45634ca8038d

import Definitions.Def_LocalOccupancyIS_Glauber_Dynamics
import Theorems.Thm_SinkhornHall_lemma_1_1

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

lemma heatBath_ratio (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (A : Finset V) (ν : State G → ℝ) {σ τ : State G}
    (he : ∀ v ∉ A, τ.val v = σ.val v) :
    push ν (heatBath G lam A) σ / HardCoreBochner.hcLaw G lam σ =
    push ν (heatBath G lam A) τ / HardCoreBochner.hcLaw G lam τ := by
  classical
  change (∑ x, ν x * heatBath G lam A x σ) / _ =
      (∑ x, ν x * heatBath G lam A x τ) / _
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  have heq : (∀ v ∉ A, σ.val v = x.val v) ↔ (∀ v ∉ A, τ.val v = x.val v) := by
    constructor
    · intro h v hv; exact (he v hv).trans (h v hv)
    · intro h v hv; exact (he v hv).symm.trans (h v hv)
  unfold heatBath
  by_cases hx : ∀ v ∉ A, σ.val v = x.val v
  · rw [if_pos hx, if_pos (heq.mp hx)]
    have hpσ := (hcLaw_pos G hlam σ).ne'
    have hpτ := (hcLaw_pos G hlam τ).ne'
    field_simp
  · rw [if_neg hx, if_neg (mt heq.mpr hx)]
    simp

lemma push_expectation_invariant {Ω : Type} [Fintype Ω] (ν : Ω → ℝ)
    {K : Matrix Ω Ω ℝ} (hK : MarkovMixing.IsStochastic K) (f : Ω → ℝ)
    (hf : ∀ x y, K x y ≠ 0 → f y = f x) :
    (∑ x, push ν K x * f x) = ∑ x, ν x * f x := by
  change (∑ x, (∑ y, ν y * K y x) * f x) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = ∑ x, ν y * K y x * f y := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : K y x = 0
      · simp [hx]
      · rw [hf y x hx]
    _ = ν y * (∑ x, K y x) * f y := by rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = _ := by rw [hK.2]; ring

lemma heatBath_entropy_identity (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (A : Finset V) {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) :
    kl ν (HardCoreBochner.hcLaw G lam) -
      kl (push ν (heatBath G lam A)) (HardCoreBochner.hcLaw G lam) =
      kl ν (push ν (heatBath G lam A)) := by
  classical
  let μ := push ν (heatBath G lam A)
  let π := HardCoreBochner.hcLaw G lam
  have hm := heatBath_dominated G hlam A hν
  have hex : ∑ x, μ x * Real.log (μ x / π x) = ∑ x, ν x * Real.log (μ x / π x) := by
    apply push_expectation_invariant ν (heatBath_stochastic G hlam A)
    intro x y hxy
    have he : ∀ v ∉ A, y.val v = x.val v := by
      by_contra hn
      exact hxy (by simp [heatBath, hn])
    rw [heatBath_ratio G hlam A ν he]
  have hs : kl ν π = kl ν μ + ∑ x, ν x * Real.log (μ x / π x) := by
    simp_rw [kl_eq_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ν x = 0
    · simp [hx]
    · have hp : π x ≠ 0 := (hcLaw_pos G hlam x).ne'
      have hμ : μ x ≠ 0 := (hm x hx).ne'
      rw [Real.log_div hx hp, Real.log_div hx hμ, Real.log_div hμ hp]
      ring
  change kl ν π - kl μ π = kl ν μ
  rw [hs, kl_eq_sum μ π, hex]
  ring

end
end LocalOccupancyIS.Glauber

open LocalOccupancyIS.Glauber

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (hlam : 0 < lam)
    (u : V) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) :
    MarkovMixing.IsDist (HardCoreBochner.hcLaw G lam) ∧
    Dominated ν (HardCoreBochner.hcLaw G lam) ∧
    ∀ A ∈ [P G lam u, Q G lam u],
      MarkovMixing.IsStochastic A ∧ Dominated ν (push ν A) ∧
      kl ν (HardCoreBochner.hcLaw G lam) - kl (push ν A) (HardCoreBochner.hcLaw G lam) =
        kl ν (push ν A) ∧ kl ν (push ν A) ≥ 2 * tv ν (push ν A) ^ 2 := by
  classical
  refine ⟨hcLaw_dist G hlam, fun σ _ => hcLaw_pos G hlam σ, ?_⟩
  have h (S : Finset V) :
      MarkovMixing.IsStochastic (heatBath G lam S) ∧
      Dominated ν (push ν (heatBath G lam S)) ∧
      kl ν (HardCoreBochner.hcLaw G lam) -
        kl (push ν (heatBath G lam S)) (HardCoreBochner.hcLaw G lam) =
        kl ν (push ν (heatBath G lam S)) ∧
      kl ν (push ν (heatBath G lam S)) ≥ 2 * tv ν (push ν (heatBath G lam S)) ^ 2 := by
    have hs := heatBath_stochastic G hlam S
    have hd := heatBath_dominated G hlam S hν
    exact ⟨hs, hd, heatBath_entropy_identity G hlam S hν,
      finite_pinsker hν (push_dist hν hs) hd⟩
  intro A hA
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl
  · exact h {u}
  · exact h (G.neighborFinset u)
