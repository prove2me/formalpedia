-- Prove2me | solution 1 for MitigateSupplyRisk.DualSourcing.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T08:07:45.965017+00:00
-- url     : https://prove2.me/submissions/ba6e801b-35a6-41d4-a98a-8e9ccb3ab939

import Mathlib
import Definitions.Def_MitigateSupplyRisk_DualSourcing_Model
open MeasureTheory ProbabilityTheory
open MitigateSupplyRisk.DualSourcing
set_option autoImplicit false

namespace SupplySubmodularity

def quantity (M : Model) (q ξ : Fin 2 → ℝ) : ℝ :=
  ∑ i, Model.deliv (M.K i) (q i) (ξ i)

def charge (M : Model) (q ξ : Fin 2 → ℝ) : ℝ :=
  ∑ i, (M.η i * q i + (1 - M.η i) * Model.deliv (M.K i) (q i) (ξ i)) * M.c i

lemma revenue_identity (r v p x y : ℝ) :
    r * min x y + v * max (y-x) 0 - p * max (x-y) 0 =
      (r+p)*y - (r+p-v)*max (y-x) 0 - p*x := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring

lemma profit_identity (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ) :
    M.profit q ξ x = -charge M q ξ + (M.r+M.p)*quantity M q ξ -
      (M.r+M.p-M.v)*max (quantity M q ξ-x) 0 - M.p*x := by
  have h := revenue_identity M.r M.v M.p x (quantity M q ξ)
  unfold Model.profit charge quantity at *
  linarith

lemma quantity_mono (M : Model) (q q' ξ : Fin 2 → ℝ) (h : q ≤ q') :
    quantity M q ξ ≤ quantity M q' ξ := by
  apply Finset.sum_le_sum
  intro i _
  exact min_le_min_right _ (h i)

lemma quantity_balance (M : Model) (q q' ξ : Fin 2 → ℝ) :
    quantity M (q ⊔ q') ξ + quantity M (q ⊓ q') ξ =
      quantity M q ξ + quantity M q' ξ := by
  unfold quantity
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases le_total (q i) (q' i) with h | h
  · simp [Pi.sup_apply, Pi.inf_apply, max_eq_right h, min_eq_left h, add_comm]
  · simp [Pi.sup_apply, Pi.inf_apply, max_eq_left h, min_eq_right h]

lemma charge_balance (M : Model) (q q' ξ : Fin 2 → ℝ) :
    charge M (q ⊔ q') ξ + charge M (q ⊓ q') ξ = charge M q ξ + charge M q' ξ := by
  unfold charge
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases le_total (q i) (q' i) with h | h
  · simp [Pi.sup_apply, Pi.inf_apply, max_eq_right h, min_eq_left h, add_comm]
  · simp [Pi.sup_apply, Pi.inf_apply, max_eq_left h, min_eq_right h]

lemma positive_part_inequality (a b u l x : ℝ) (ha : a ≤ u) (hb : b ≤ u)
    (he : u+l=a+b) : max (a-x) 0 + max (b-x) 0 ≤ max (u-x) 0 + max (l-x) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

lemma profit_submodular (M : Model) (q q' ξ : Fin 2 → ℝ) (x : ℝ) :
    M.profit (q ⊔ q') ξ x + M.profit (q ⊓ q') ξ x ≤ M.profit q ξ x + M.profit q' ξ x := by
  have hb := quantity_balance M q q' ξ
  have hc := charge_balance M q q' ξ
  have hp := positive_part_inequality (quantity M q ξ) (quantity M q' ξ)
    (quantity M (q ⊔ q') ξ) (quantity M (q ⊓ q') ξ) x
    (quantity_mono M q (q ⊔ q') ξ le_sup_left)
    (quantity_mono M q' (q ⊔ q') ξ le_sup_right) hb
  have hm := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr M.v_lt.le)
  have he := congrArg (fun z : ℝ => (M.r+M.p)*z) hb
  simp only [profit_identity]
  nlinarith only [hc, hm, he]

lemma profit_integrable (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμint : Integrable id μ) (a q : Fin 2 → ℝ) (hq : q ∈ Model.orders) :
    Integrable (fun ω => M.profit q ω.1 ω.2) ((Measure.pi fun i => M.ν i (a i)).prod μ) := by
  let ν := (Measure.pi fun i => M.ν i (a i)).prod μ
  have hd (i : Fin 2) : Integrable (fun ω : (Fin 2 → ℝ) × ℝ =>
      Model.deliv (M.K i) (q i) (ω.1 i)) ν := by
    apply (integrable_const (q i)).mono'
    · apply Continuous.aestronglyMeasurable
      unfold Model.deliv
      fun_prop
    · apply ae_of_all
      intro ω
      unfold Model.deliv
      rw [Real.norm_of_nonneg (le_min (hq i) (le_max_right _ _))]
      exact min_le_left _ _
  have hy : Integrable (fun ω : (Fin 2 → ℝ) × ℝ => quantity M q ω.1) ν :=
    integrable_finsetSum _ (fun i _ => hd i)
  have hc : Integrable (fun ω : (Fin 2 → ℝ) × ℝ => charge M q ω.1) ν :=
    integrable_finsetSum _ (fun i _ =>
      ((integrable_const (M.η i * q i)).add ((hd i).const_mul (1-M.η i))).mul_const (M.c i))
  have hx : Integrable (fun ω : (Fin 2 → ℝ) × ℝ => ω.2) ν := hμint.comp_snd _
  have hz : Integrable (fun _ : (Fin 2 → ℝ) × ℝ => (0 : ℝ)) ν := integrable_const 0
  change Integrable _ ν
  have h := ((hc.neg.add ((hx.inf hy).const_mul M.r)).add
    (((hy.sub hx).sup hz).const_mul M.v)).sub (((hx.sub hy).sup hz).const_mul M.p)
  apply h.congr
  apply ae_of_all
  intro ω
  rfl

end SupplySubmodularity

theorem solution (M : Model) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) (a : Fin 2 → ℝ)
    (q q' : Fin 2 → ℝ) (hq : q ∈ Model.orders) (hq' : q' ∈ Model.orders) :
    M.Pi2 μ (q ⊔ q') a + M.Pi2 μ (q ⊓ q') a ≤ M.Pi2 μ q a + M.Pi2 μ q' a := by
  have hsup : q ⊔ q' ∈ Model.orders := fun i => le_trans (hq i) (le_max_left _ _)
  have hinf : q ⊓ q' ∈ Model.orders := fun i => le_min (hq i) (hq' i)
  have hqI := SupplySubmodularity.profit_integrable M μ hμint a q hq
  have hq'I := SupplySubmodularity.profit_integrable M μ hμint a q' hq'
  have hsI := SupplySubmodularity.profit_integrable M μ hμint a (q ⊔ q') hsup
  have hiI := SupplySubmodularity.profit_integrable M μ hμint a (q ⊓ q') hinf
  unfold Model.Pi2
  rw [← integral_add hsI hiI, ← integral_add hqI hq'I]
  exact integral_mono (hsI.add hiI) (hqI.add hq'I)
    (fun ω => SupplySubmodularity.profit_submodular M q q' ω.1 ω.2)

#print axioms solution
