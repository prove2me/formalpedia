-- Prove2me | solution 1 for JobShopLTAS.Core.optMakespan_le_m_mul_Pmax
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:16:49.874798+00:00
-- url     : https://prove2.me/submissions/6d3b314c-3378-4359-a6fb-59c57505532b

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance

open JobShopLTAS.Core

private def beforeOp {m n : ℕ} {inst : Instance m n} (o₁ o₂ : inst.Op) : Prop :=
  o₁.1.val < o₂.1.val ∨ (o₁.1.val = o₂.1.val ∧ o₁.2.val < o₂.2.val)

private instance {m n : ℕ} {inst : Instance m n} : DecidableRel (beforeOp (inst := inst)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private noncomputable def sSer {m n : ℕ} (inst : Instance m n) (o : inst.Op) : ℝ :=
  ∑ o' ∈ Finset.univ.filter (fun o' : inst.Op => beforeOp o' o), inst.proc o'

private lemma sSer_step {m n : ℕ} (inst : Instance m n) {o₁ o₂ : inst.Op}
    (h : beforeOp o₁ o₂) :
    sSer inst o₁ + inst.proc o₁ ≤ sSer inst o₂ := by
  have hnot : o₁ ∉ Finset.univ.filter (fun o' : inst.Op => beforeOp o' o₁) := by
    simp [beforeOp]
  unfold sSer
  rw [add_comm, ← Finset.sum_insert hnot]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro o' ho'
    rw [Finset.mem_insert, Finset.mem_filter] at ho'
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ho' with rfl | ⟨_, h'⟩
    · exact h
    · unfold beforeOp at h h' ⊢
      omega
  · intro o' _ _
    exact inst.p_nonneg o'.1 o'.2

private lemma sSer_feasible {m n : ℕ} (inst : Instance m n) :
    inst.IsFeasibleSchedule Finset.univ (sSer inst) where
  start_nonneg o _ := Finset.sum_nonneg (fun o' _ => inst.p_nonneg o'.1 o'.2)
  precedence j _ i i' hii' := by
    apply sSer_step inst (o₁ := ⟨j, i⟩) (o₂ := ⟨j, i'⟩)
    exact Or.inr ⟨rfl, by dsimp; omega⟩
  machine_disjoint o o' _ _ hne _ := by
    have htrich : beforeOp o o' ∨ beforeOp o' o := by
      unfold beforeOp
      by_cases h1 : o.1.val = o'.1.val
      · have h2 : o.2.val ≠ o'.2.val := by
          intro h2
          apply hne
          rcases o with ⟨j₁, i₁⟩
          rcases o' with ⟨j₂, i₂⟩
          have hj : j₁ = j₂ := Fin.ext h1
          subst hj
          congr
          exact Fin.ext h2
        omega
      · omega
    rcases htrich with h | h
    · exact Or.inl (sSer_step inst h)
    · exact Or.inr (sSer_step inst h)

private lemma sum_proc_le_m_mul_Pmax {m n : ℕ} (inst : Instance m n) :
    (∑ o : inst.Op, inst.proc o) ≤ (m : ℝ) * inst.Pmax := by
  have hfib : (∑ o : inst.Op, inst.proc o) = ∑ t : Fin m, inst.load t := by
    unfold Instance.load
    exact (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) inst.proc).symm
  rw [hfib]
  have hle : ∑ t : Fin m, inst.load t ≤ ∑ _t : Fin m, inst.Pmax := by
    apply Finset.sum_le_sum
    intro t _
    exact le_ciSup (Set.finite_range _).bddAbove t
  simpa using hle

private lemma makespan_nonneg {m n : ℕ} (inst : Instance m n) (s : inst.Op → ℝ)
    (hs : inst.IsFeasibleSchedule Finset.univ s) :
    0 ≤ inst.makespan Finset.univ s := by
  unfold Instance.makespan
  by_cases h : Nonempty {o : inst.Op // o.1 ∈ (Finset.univ : Finset (Fin n))}
  · rcases h with ⟨⟨o₀, ho₀⟩⟩
    have h0 : 0 ≤ s o₀ + inst.proc o₀ :=
      add_nonneg (hs.start_nonneg o₀ ho₀) (inst.p_nonneg o₀.1 o₀.2)
    exact le_trans h0 (le_ciSup (f := fun o : {o : inst.Op // o.1 ∈ (Finset.univ : Finset (Fin n))} => s o.1 + inst.proc o.1) (Set.finite_range _).bddAbove ⟨o₀, ho₀⟩)
  · rw [not_nonempty_iff] at h
    simp

theorem solution {m n : ℕ} (inst : Instance m n) :
    inst.optMakespan Finset.univ ≤ (m : ℝ) * inst.Pmax := by
  have hbdd : BddBelow (inst.makespan Finset.univ '' {s | inst.IsFeasibleSchedule Finset.univ s}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact makespan_nonneg inst s hs
  have hle : inst.optMakespan Finset.univ ≤ inst.makespan Finset.univ (sSer inst) :=
    csInf_le hbdd ⟨sSer inst, sSer_feasible inst, rfl⟩
  refine le_trans hle (le_trans ?_ (sum_proc_le_m_mul_Pmax inst))
  unfold Instance.makespan
  by_cases h : Nonempty {o : inst.Op // o.1 ∈ (Finset.univ : Finset (Fin n))}
  · apply ciSup_le
    rintro ⟨o, _⟩
    dsimp
    unfold sSer
    have hnot : o ∉ Finset.univ.filter (fun o' : inst.Op => beforeOp o' o) := by
      simp [beforeOp]
    rw [add_comm, ← Finset.sum_insert hnot]
    exact Finset.sum_le_univ_sum_of_nonneg (fun o' => inst.p_nonneg o'.1 o'.2)
  · rw [not_nonempty_iff] at h
    simp
    exact Finset.sum_nonneg (fun o' _ => inst.p_nonneg o'.1 o'.2)
