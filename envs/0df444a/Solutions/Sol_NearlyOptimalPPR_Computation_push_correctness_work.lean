-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.push_correctness_work
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:10:58.244902+00:00
-- url     : https://prove2.me/submissions/a8876e85-46bf-4468-b47b-646f72dc88ba

import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_residual_error

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

variable {n : ℕ}

lemma input_degree (g : InputGraph n) (v : Fin n) :
    (g.neighbors v).length = g.graph.degree v := by
  have he : (g.neighbors v).toFinset = g.graph.neighborFinset v := by
    ext u
    simp [g.correct]
  rw [← List.toFinset_card_of_nodup (g.nodup v), he,
    SimpleGraph.card_neighborFinset_eq_degree]

lemma output_sparseOn (T : Finset (Fin n)) (x : Fin n → ℝ) (v : Fin n) :
    outputVector (sparseOn T x) v = if v ∈ T then x v else 0 := by
  classical
  simp only [outputVector, sparseOn, List.map_map, Function.comp_apply]
  have he : ∀ u : Fin n, ((u.val : ℤ) = (v.val : ℤ)) ↔ u = v := by
    intro u
    simp only [Int.natCast_inj, Fin.val_inj]
  rw [← List.sum_toFinset _ (T.nodup_toList.filter _)]
  simp only [List.toFinset_filter]
  by_cases hx : x v = 0 <;> by_cases hv : v ∈ T <;>
    simp [Finset.sum_filter, he, Int.natCast_inj, Fin.val_inj, hx, hv]

lemma push_residual_update (g : InputGraph n) (s v : Fin n) (α : ℝ)
    (z r : Fin n → ℝ) (hr : r = residual g.graph α s z)
    (hd : 0 < g.graph.degree v) :
    residual g.graph α s (Function.update z v (z v + r v / LocalPush.deg g.graph v)) =
      fun u => (if u = v then 0 else r u) +
        if u ∈ g.neighbors v then (1 - α) * (r v / LocalPush.deg g.graph v) else 0 := by
  classical
  let h := r v / LocalPush.deg g.graph v
  have hz : Function.update z v (z v + h) = z + Pi.single v h := by
    ext u
    by_cases hu : u = v <;> simp [hu, Pi.single_apply]
  change residual g.graph α s (Function.update z v (z v + h)) = _
  rw [hz]
  ext u
  have hru := congrFun hr u
  simp only [residual, Pi.sub_apply] at hru ⊢
  rw [Matrix.mulVec_add, Matrix.mulVec_single]
  change LocalPush.e s u - ((LocalPush.Lα g.graph α *ᵥ z) u +
      LocalPush.Lα g.graph α u v * h) = _
  have hd0 : LocalPush.deg g.graph v ≠ 0 := by
    unfold LocalPush.deg
    exact_mod_cast hd.ne'
  have hmuv : LocalPush.Lα g.graph α u v =
      (if u = v then LocalPush.deg g.graph v else 0) -
        (1-α) * (if g.graph.Adj u v then 1 else 0) := by
    by_cases hu : u = v <;> simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM,
      SimpleGraph.adjMatrix_apply, Matrix.diagonal_apply, hu]
  rw [hmuv]
  simp only [g.correct]
  by_cases hu : u = v
  · subst u
    simp only [ite_true, SimpleGraph.irrefl, ite_false, mul_zero, sub_zero, add_zero]
    dsimp [h]
    field_simp
    linarith [hru]
  · by_cases ha : g.graph.Adj v u
    · have ha' := ha.symm
      simp only [hu, ite_false, ha, ha', ite_true, mul_one, zero_sub]
      dsimp [h]
      linarith [hru]
    · have ha' : ¬ g.graph.Adj u v := fun h => ha h.symm
      simp only [hu, ite_false, ha, ha', mul_zero, sub_zero, zero_mul, add_zero]
      exact hru.symm

lemma push_mass_update (g : InputGraph n) (α : ℝ) (r : Fin n → ℝ)
    (v : Fin n) (hd : 0 < g.graph.degree v) :
    (∑ u, ((if u = v then 0 else r u) +
      if u ∈ g.neighbors v then (1 - α) * (r v / LocalPush.deg g.graph v) else 0)) =
        (∑ u, r u) - α * r v := by
  classical
  have ha : (Finset.univ.filter (fun u => u ∈ g.neighbors v)) = g.graph.neighborFinset v := by
    ext u
    simp [g.correct]
  have hh : ∑ u, (if u = v then (0 : ℝ) else r u) = (∑ u, r u) - r v := by
    have he : (fun u => if u = v then (0 : ℝ) else r u) = r - Pi.single v (r v) := by
      ext u
      by_cases hu : u = v <;> simp [hu, Pi.single_apply]
    simp [he, Finset.sum_sub_distrib, Pi.single_apply]
  rw [Finset.sum_add_distrib, hh]
  rw [← Finset.sum_filter, ha]
  simp only [Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
  have hd0 : LocalPush.deg g.graph v ≠ 0 := by unfold LocalPush.deg; exact_mod_cast hd.ne'
  change _ + LocalPush.deg g.graph v * ((1-α) * (r v / LocalPush.deg g.graph v)) = _
  field_simp
  <;> ring

structure PushInvariant (g : InputGraph n) (s : Fin n) (α ε : ℝ) (st : PushState n) : Prop where
  z_nonneg : ∀ v, 0 ≤ st.z v
  r_nonneg : ∀ v, 0 ≤ st.r v
  residual_eq : st.r = residual g.graph α s st.z
  queue_nodup : st.queue.Nodup
  queued_eq : st.queued = st.queue.toFinset
  queue_positive : ∀ v ∈ st.queue, 0 < g.graph.degree v
  high_queued : ∀ v, ε * LocalPush.deg g.graph v < st.r v → v ∈ st.queue
  support_z : ∀ v ∉ st.support, st.z v = 0
  done_queue : st.done = true → st.queue = []
  done_output : st.done = true →
    st.output = sparseOn st.support (potentialOutput g.graph α st.z)

lemma push_init_invariant (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hε : 0 < ε) (hs : 0 < g.graph.degree s) :
    PushInvariant g s α ε (pushInit s) := by
  classical
  constructor
  · simp [pushInit]
  · intro v
    simp only [pushInit, LocalPush.e, Pi.single_apply]
    split <;> norm_num
  · simp [pushInit, residual, show (fun _ : Fin n => (0 : ℝ)) = 0 from rfl]
  · simp [pushInit]
  · simp [pushInit]
  · simpa [pushInit] using hs
  · intro v hv
    by_cases h : v = s
    · simpa [pushInit] using h
    · have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
      simp [pushInit, LocalPush.e, Pi.single_apply, h] at hv
      exact (not_lt_of_ge (mul_nonneg hε.le hd) hv).elim
  · simp [pushInit]
  · simp [pushInit]
  · simp [pushInit]

lemma push_step_invariant (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε) (st : PushState n)
    (hi : PushInvariant g s α ε st) :
    PushInvariant g s α ε (pushStep g α ε st) := by
  classical
  by_cases hd : st.done = true
  · simpa [pushStep, hd] using hi
  cases hq : st.queue with
  | nil =>
    simp only [pushStep, hd, Bool.false_eq_true, ↓reduceIte, hq]
    exact ⟨hi.z_nonneg, hi.r_nonneg, hi.residual_eq, by simp,
      by simpa [hq] using hi.queued_eq, by simp,
      by simpa [hq] using hi.high_queued, hi.support_z, by simp, by simp⟩
  | cons v rest =>
    have hn : v ∉ rest ∧ rest.Nodup := by simpa [hq] using hi.queue_nodup
    have hvpos : 0 < g.graph.degree v := hi.queue_positive v (by simp [hq])
    have hQ : st.queued.erase v = rest.toFinset := by
      simp [hi.queued_eq, hq, hn.1]
    by_cases ha : ε * LocalPush.deg g.graph v < st.r v
    · let r' : Fin n → ℝ := fun u => (if u = v then 0 else st.r u) +
        if u ∈ g.neighbors v then (1 - α) * (st.r v / LocalPush.deg g.graph v) else 0
      let added := (g.neighbors v).filter fun u =>
        u ∉ st.queued.erase v ∧ ε * LocalPush.deg g.graph u < r' u
      have hrpos : ∀ u, 0 ≤ r' u := by
        intro u
        have hr := hi.r_nonneg u
        have hrv := hi.r_nonneg v
        have hnon : 0 ≤ 1 - α := sub_nonneg.mpr hα.2.le
        have hdg : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
        dsimp [r']
        split <;> split <;> positivity
      have hrself : r' v = 0 := by simp [r', g.correct]
      have hadded : ∀ u, u ∈ added ↔
          u ∈ g.neighbors v ∧ u ∉ rest ∧ ε * LocalPush.deg g.graph u < r' u := by
        intro u
        simp [added, hQ, and_assoc]
      have hhq : ∀ u, ε * LocalPush.deg g.graph u < r' u → u ∈ rest ++ added := by
        intro u hu
        by_cases hur : u ∈ rest
        · simp [hur]
        · apply List.mem_append.mpr
          right
          apply (hadded u).mpr
          refine ⟨?_, hur, hu⟩
          by_contra hun
          by_cases huv : u = v
          · subst u
            rw [hrself] at hu
            have hdg : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
            exact (not_lt_of_ge (mul_nonneg hε.le hdg) hu)
          · have hrold : r' u = st.r u := by simp [r', huv, hun]
            have hold := hi.high_queued u (by rwa [hrold] at hu)
            simpa [hq, huv, hur] using hold
      simp only [pushStep, hd, Bool.false_eq_true, ↓reduceIte, hq, ha]
      change PushInvariant g s α ε
        ⟨Function.update st.z v (st.z v + st.r v / LocalPush.deg g.graph v),
          r', rest ++ added, st.queued.erase v ∪ added.toFinset,
          insert v st.support, _, [], false⟩
      constructor
      · intro u
        by_cases hu : u = v
        · subst u
          simp only [Function.update_self]
          exact add_nonneg (hi.z_nonneg v) (div_nonneg (hi.r_nonneg v) (by unfold LocalPush.deg; positivity))
        · simpa [hu] using hi.z_nonneg u
      · exact hrpos
      · exact (push_residual_update g s v α st.z st.r hi.residual_eq hvpos).symm
      · apply List.nodup_append.mpr
        refine ⟨hn.2, (g.nodup v).filter _, ?_⟩
        intro u hu w hw he
        subst w
        exact ((hadded u).mp hw).2.1 hu
      · simp [hQ]
      · intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hi.queue_positive u (by simp [hq, hu])
        · exact ((g.correct v u).mp ((hadded u).mp hu).1).degree_pos_right
      · exact hhq
      · intro u hu
        have hu' : u ≠ v ∧ u ∉ st.support := by simpa using hu
        simpa [hu'.1] using hi.support_z u hu'.2
      · simp
      · simp
    · simp only [pushStep, hd, Bool.false_eq_true, ↓reduceIte, hq, ha]
      constructor
      · exact hi.z_nonneg
      · exact hi.r_nonneg
      · exact hi.residual_eq
      · exact hn.2
      · exact hQ
      · intro u hu
        exact hi.queue_positive u (by simp [hq, hu])
      · intro u hu
        have hold := hi.high_queued u hu
        have huv : u ≠ v := by intro he; subst u; exact ha hu
        simpa [hq, huv] using hold
      · exact hi.support_z
      · simp
      · simp

lemma push_run_invariant (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε) (hs : 0 < g.graph.degree s) (t : ℕ) :
    PushInvariant g s α ε (pushRun g s α ε t) := by
  induction t with
  | zero => simpa [pushRun] using push_init_invariant g s α ε hε hs
  | succ t ih =>
    simpa only [pushRun, Function.iterate_succ_apply'] using
      push_step_invariant g s α ε hα hε (pushRun g s α ε t) ih

def pushCredits (st : PushState n) : ℕ :=
  st.work + 4 * st.queue.length + if st.done then 0 else 4 * st.support.card + 1

def pushPotential (α ε : ℝ) (st : PushState n) : ℝ :=
  α * ε * (pushCredits st : ℝ) + 80 * ∑ v, st.r v

lemma push_potential_step (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε) (st : PushState n)
    (hi : PushInvariant g s α ε st) :
    pushPotential α ε (pushStep g α ε st) ≤ pushPotential α ε st := by
  classical
  by_cases hd : st.done = true
  · simp [pushStep, hd]
  cases hq : st.queue with
  | nil =>
    simp only [pushPotential, pushCredits, pushStep, hd, Bool.false_eq_true,
      ↓reduceIte, hq, List.length_nil, mul_zero, add_zero, Bool.true_eq_false]
    push_cast
    ring_nf
    rfl
  | cons v rest =>
    have hvpos : 0 < g.graph.degree v := hi.queue_positive v (by simp [hq])
    by_cases ha : ε * LocalPush.deg g.graph v < st.r v
    · have hc : pushCredits (pushStep g α ε st) ≤
          pushCredits st + 80 * g.graph.degree v := by
        have hl : ((g.neighbors v).filter fun u =>
          u ∉ st.queued.erase v ∧ ε * LocalPush.deg g.graph u <
            ((if u = v then 0 else st.r u) +
              if u ∈ g.neighbors v then (1-α) * (st.r v / LocalPush.deg g.graph v) else 0)).length ≤
            g.graph.degree v := by
          simpa only [input_degree] using List.length_filter_le
            (l := g.neighbors v) (p := fun u => decide (u ∉ st.queued.erase v ∧
              ε * LocalPush.deg g.graph u < ((if u = v then 0 else st.r u) +
                if u ∈ g.neighbors v then (1-α) * (st.r v / LocalPush.deg g.graph v) else 0)))
        have hs := Finset.card_insert_le v st.support
        simp only [pushCredits, pushStep, hd, Bool.false_eq_true, ↓reduceIte,
          hq, ha, List.length_cons, List.length_append, input_degree]
        omega
      have hmass : (∑ v, (pushStep g α ε st).r v) = (∑ v, st.r v) - α * st.r v := by
        simp only [pushStep, hd, Bool.false_eq_true, ↓reduceIte, hq, ha]
        exact push_mass_update g α st.r v hvpos
      have hcc : (pushCredits (pushStep g α ε st) : ℝ) ≤
          (pushCredits st : ℝ) + 80 * LocalPush.deg g.graph v := by
        unfold LocalPush.deg
        exact_mod_cast hc
      have hmul := mul_le_mul_of_nonneg_left hcc (mul_nonneg hα.1.le hε.le)
      have hdec := mul_le_mul_of_nonneg_left ha.le hα.1.le
      simp only [pushPotential, hmass]
      nlinarith
    · simp only [pushPotential, pushCredits, pushStep, hd, Bool.false_eq_true,
        ↓reduceIte, hq, ha, List.length_cons]
      push_cast
      ring_nf
      rfl

lemma push_work_bound (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1)
    (hs : 0 < g.graph.degree s) (t : ℕ) :
    ((pushRun g s α ε t).work : ℝ) ≤ 100 / (α * ε) := by
  have hp : ∀ t, pushPotential α ε (pushRun g s α ε t) ≤
      pushPotential α ε (pushInit s) := by
    intro t
    induction t with
    | zero => simp [pushRun]
    | succ t ih =>
      calc
        _ ≤ pushPotential α ε (pushRun g s α ε t) := by
          simpa only [pushRun, Function.iterate_succ_apply'] using
            push_potential_step g s α ε hα hε.1 _ (push_run_invariant g s α ε hα hε.1 hs t)
        _ ≤ _ := ih
  have hinit : pushPotential α ε (pushInit s) = 9 * α * ε + 80 := by
    simp [pushPotential, pushCredits, pushInit, LocalPush.e, Pi.single_apply]
    ring
  have hi := push_run_invariant g s α ε hα hε.1 hs t
  have hr : 0 ≤ ∑ v, (pushRun g s α ε t).r v :=
    Finset.sum_nonneg fun v _ => hi.r_nonneg v
  have hc : (pushRun g s α ε t).work ≤ pushCredits (pushRun g s α ε t) := by
    unfold pushCredits
    omega
  have hc' : ((pushRun g s α ε t).work : ℝ) ≤ (pushCredits (pushRun g s α ε t) : ℝ) := by
    exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hc' (mul_nonneg hα.1.le hε.1.le)
  have haε : α * ε ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hα.2.le) hε.1.le]
  have hpt := hp t
  rw [hinit] at hpt
  unfold pushPotential at hpt
  apply (le_div_iff₀ (mul_pos hα.1 hε.1)).mpr
  nlinarith

lemma push_work_increases (g : InputGraph n) (α ε : ℝ) (st : PushState n)
    (hd : st.done ≠ true) : st.work + 1 ≤ (pushStep g α ε st).work := by
  classical
  cases hdone : st.done with
  | true => exact (hd hdone).elim
  | false =>
    cases hq : st.queue with
    | nil => simp [pushStep, hdone, hq]
    | cons v rest =>
      by_cases ha : ε * LocalPush.deg g.graph v < st.r v
      · simp [pushStep, hdone, hq, ha]
        omega
      · simp [pushStep, hdone, hq, ha]

lemma push_terminates (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1)
    (hs : 0 < g.graph.degree s) :
    ∃ t, (pushRun g s α ε t).done = true := by
  by_contra hn
  push_neg at hn
  have hinc : ∀ t, t ≤ (pushRun g s α ε t).work := by
    intro t
    induction t with
    | zero => omega
    | succ t ih =>
      have hh := push_work_increases g α ε (pushRun g s α ε t) (hn t)
      have he : pushRun g s α ε (t + 1) = pushStep g α ε (pushRun g s α ε t) := by
        simp only [pushRun, Function.iterate_succ_apply']
      rw [he]
      omega
  obtain ⟨t, ht⟩ := exists_nat_gt (100 / (α * ε))
  have ht' : (t : ℝ) ≤ ((pushRun g s α ε t).work : ℝ) := by exact_mod_cast hinc t
  have hb := push_work_bound g s α ε hα hε hs t
  linarith

lemma push_work_ennreal (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1)
    (hs : 0 < g.graph.degree s) :
    pushWork g s α ε ≤ ENNReal.ofReal (100 / (α * ε)) := by
  classical
  simp only [pushWork, if_pos (push_terminates g s α ε hα hε hs)]
  apply iSup_le
  intro t
  have h := ENNReal.ofReal_le_ofReal (push_work_bound g s α ε hα hε hs t)
  simpa only [ENNReal.ofReal_natCast] using h

lemma push_correct (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1)
    (hs : 0 < g.graph.degree s) :
    ∃ t : ℕ,
      (pushRun g s α ε t).done = true ∧
      (∀ v, 0 ≤ (pushRun g s α ε t).z v) ∧
      (∀ v, 0 ≤ residual g.graph α s (pushRun g s α ε t).z v ∧
        residual g.graph α s (pushRun g s α ε t).z v ≤ ε * LocalPush.deg g.graph v) ∧
      outputVector (pushRun g s α ε t).output =
        potentialOutput g.graph α (pushRun g s α ε t).z ∧
      ACL g.graph α ε s (outputVector (pushRun g s α ε t).output) := by
  obtain ⟨t, ht⟩ := push_terminates g s α ε hα hε hs
  have hi := push_run_invariant g s α ε hα hε.1 hs t
  have hr : ∀ v, 0 ≤ residual g.graph α s (pushRun g s α ε t).z v ∧
      residual g.graph α s (pushRun g s α ε t).z v ≤ ε * LocalPush.deg g.graph v := by
    intro v
    rw [← hi.residual_eq]
    refine ⟨hi.r_nonneg v, ?_⟩
    by_contra hv
    have hh := hi.high_queued v (lt_of_not_ge hv)
    simpa [hi.done_queue ht] using hh
  have ho : outputVector (pushRun g s α ε t).output =
      potentialOutput g.graph α (pushRun g s α ε t).z := by
    rw [hi.done_output ht]
    ext v
    rw [output_sparseOn]
    by_cases hv : v ∈ (pushRun g s α ε t).support
    · simp [hv]
    · simp [hv, potentialOutput, hi.support_z v hv]
  refine ⟨t, ht, hi.z_nonneg, hr, ho, ?_⟩
  rw [ho]
  exact (residual_error g.graph s α ε hα hε hs _ hi.z_nonneg).2 hr

end
end NearlyOptimalPPR.Computation

open NearlyOptimalPPR.Computation

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0 < α → α < 1 → 0 < ε → ε ≤ 1 → 0 < g.graph.degree s →
          pushWork g s α ε ≤ ENNReal.ofReal (C / (α * ε)) ∧
          ∃ t : ℕ,
            (pushRun g s α ε t).done = true ∧
            (∀ v, 0 ≤ (pushRun g s α ε t).z v) ∧
            (∀ v, 0 ≤ residual g.graph α s (pushRun g s α ε t).z v ∧
              residual g.graph α s (pushRun g s α ε t).z v ≤ ε * LocalPush.deg g.graph v) ∧
            outputVector (pushRun g s α ε t).output =
              potentialOutput g.graph α (pushRun g s α ε t).z ∧
            ACL g.graph α ε s (outputVector (pushRun g s α ε t).output) := by
  refine ⟨100, by norm_num, ?_⟩
  intro n g s α ε hα hα' hε hε' hs
  exact ⟨push_work_ennreal g s α ε ⟨hα,hα'⟩ ⟨hε,hε'⟩ hs,
    push_correct g s α ε ⟨hα,hα'⟩ ⟨hε,hε'⟩ hs⟩
