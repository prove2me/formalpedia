-- Prove2me | solution 1 for OAI.PlanarBoundary.blocked_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:44:32.003792+00:00
-- url     : https://prove2.me/submissions/751d08c4-2e3b-4069-a467-39f329922fed

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls

open OAI OAI.PlanarBoundary
universe uOmega
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Filter Topology
open Classical _root_.MeasureTheory ProbabilityTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
theorem pl_degree (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // primalInside e = v ∨ primalOutside e = v} ≤ 4 := by
  have h := Fintype.card_le_of_injective
    (fun e : {e : Boundary X // primalInside e = v ∨ primalOutside e = v} => e.val.val.2) ?_
  · simpa using h
  rintro ⟨⟨⟨p, d⟩, hp1, hp2⟩, hp⟩ ⟨⟨⟨q, d'⟩, hq1, hq2⟩, hq⟩ h
  simp only at h
  subst h
  simp only [primalInside, primalOutside] at hp hq
  have : p = q := by
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · rw [hp, hq]
    · subst hp; exact absurd (hq ▸ hp1) hq2
    · subst hq; exact absurd (hp ▸ hq1) hp2
    · exact add_right_cancel (hp.trans hq.symm)
  subst this
  rfl

theorem pl_greedy {α : Type*} [DecidableEq α] (C : α → Finset α) (hself : ∀ i, i ∈ C i)
    (hsymm : ∀ i j, j ∈ C i → i ∈ C j) (hcard : ∀ i, (C i).card ≤ 7) :
    ∀ T : Finset α, ∃ S ⊆ T, T.card ≤ 7 * S.card ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → j ∉ C i := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
  rcases T.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · exact ⟨∅, by simp, by simp, by simp⟩
  · have hss : T \ C i ⊂ T :=
      ⟨Finset.sdiff_subset, fun h => (Finset.mem_sdiff.1 (h hi)).2 (hself i)⟩
    obtain ⟨S', hS'sub, hS'card, hS'pw⟩ := ih (T \ C i) hss
    have hiS' : i ∉ S' := fun h => (Finset.mem_sdiff.1 (hS'sub h)).2 (hself i)
    refine ⟨insert i S', Finset.insert_subset hi (hS'sub.trans Finset.sdiff_subset), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hiS']
      have := Finset.card_le_card_sdiff_add_card (s := T) (t := C i)
      have := hcard i
      omega
    · intro a ha b hb hab
      rcases Finset.mem_insert.1 ha with rfl | ha' <;> rcases Finset.mem_insert.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact (Finset.mem_sdiff.1 (hS'sub hb')).2
      · intro h
        exact (Finset.mem_sdiff.1 (hS'sub ha')).2 (hsymm _ _ h)
      · exact hS'pw a ha' b hb' hab

theorem solution {n : ℕ} (Bad : Point → Set Ω) (c : Code n) (hc : Valid c)
    {f : ℝ} (hf0 : 0 < f) (hf1 : 2*f ≤ 1)
    (hbad : ∀ s : Finset Point, μ.real {ω | ∀ v ∈ s, ω ∈ Bad v} ≤ f^s.card) :
    μ.real (blocked Bad c) ≤ (2*f)^((n : ℝ)/7) := by
  obtain ⟨X, e, hinj, htr⟩ := hc
  have hin : ∀ i, PlanarBoundary.inner c i = (e i).val.1 := by intro i; simp [PlanarBoundary.inner, htr i]
  have hout : ∀ i, outer c i = (e i).val.1 + outward (e i).val.2 := by intro i; simp [outer, htr i]
  let N : Point → Finset (Fin n) := fun v =>
    Finset.univ.filter (fun j => (e j).val.1 = v ∨ (e j).val.1 + outward (e j).val.2 = v)
  have hN : ∀ v, (N v).card ≤ 4 := by
    intro v
    have h1 : (N v).card ≤ (Finset.univ.filter (fun b : Boundary X => primalInside b = v ∨ primalOutside b = v)).card := by
      apply Finset.card_le_card_of_injOn e
      · intro j hj
        simp only [N, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by simpa [primalInside, primalOutside] using hj⟩
      · exact hinj.injOn
    have h2 := pl_degree X v
    rw [Fintype.card_subtype] at h2
    exact h1.trans (le_of_eq_of_le (by congr) h2)
  let C : Fin n → Finset (Fin n) := fun i => N (e i).val.1 ∪ N ((e i).val.1 + outward (e i).val.2)
  have hself : ∀ i, i ∈ C i := by intro i; simp [C, N]
  have hsymm : ∀ i j, j ∈ C i → i ∈ C j := by
    intro i j h
    simp only [C, N, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    rcases h with (h|h)|(h|h)
    · exact Or.inl (Or.inl h.symm)
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inl (Or.inr h.symm)
    · exact Or.inr (Or.inr h.symm)
  have hcard : ∀ i, (C i).card ≤ 7 := by
    intro i
    have h1 := Finset.card_union_add_card_inter (N (e i).val.1) (N ((e i).val.1 + outward (e i).val.2))
    have h2 : 0 < (N (e i).val.1 ∩ N ((e i).val.1 + outward (e i).val.2)).card :=
      Finset.card_pos.2 ⟨i, by simp [N]⟩
    have := hN (e i).val.1
    have := hN ((e i).val.1 + outward (e i).val.2)
    simp only [C]
    omega
  obtain ⟨S, -, hScard, hSpw⟩ := pl_greedy C hself hsymm hcard Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hScard
  let vσ : (S → Bool) → S → Point := fun σ i => if σ i then PlanarBoundary.inner c i.val else outer c i.val
  have hsub : blocked Bad c ⊆ ⋃ σ : S → Bool, {ω | ∀ v ∈ (Finset.univ : Finset S).image (vσ σ), ω ∈ Bad v} := by
    intro ω hω
    simp only [Set.mem_iUnion]
    refine ⟨fun i => decide (ω ∈ Bad (PlanarBoundary.inner c i.val)), ?_⟩
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    by_cases h : ω ∈ Bad (PlanarBoundary.inner c i.val)
    · simp [vσ, h]
    · simp only [vσ, h, decide_false]
      exact (hω i.val).resolve_left h
  have hcimg : ∀ σ, ((Finset.univ : Finset S).image (vσ σ)).card = S.card := by
    intro σ
    rw [Finset.card_image_of_injective _ ?_]
    · simp
    intro i j hij
    by_contra hne
    have hji : j.val ∉ C i.val := hSpw i.val i.2 j.val j.2 (fun h => hne (Subtype.ext h))
    apply hji
    simp only [vσ] at hij
    simp only [C, N, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hin, hin, hout, hout] at hij
    by_cases hi : σ i <;> by_cases hj : σ j <;> simp only [hi, hj, if_true, if_false, Bool.false_eq_true] at hij
    · exact Or.inl (Or.inl hij.symm)
    · exact Or.inl (Or.inr hij.symm)
    · exact Or.inr (Or.inl hij.symm)
    · exact Or.inr (Or.inr hij.symm)
  have hbd : μ.real (blocked Bad c) ≤ (2*f)^S.card := by
    calc μ.real (blocked Bad c) ≤ μ.real (⋃ σ : S → Bool, {ω | ∀ v ∈ (Finset.univ : Finset S).image (vσ σ), ω ∈ Bad v}) :=
          measureReal_mono hsub
      _ ≤ ∑ σ : S → Bool, μ.real {ω | ∀ v ∈ (Finset.univ : Finset S).image (vσ σ), ω ∈ Bad v} :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ σ : S → Bool, f^S.card := by
          apply Finset.sum_le_sum
          intro σ _
          have := hbad ((Finset.univ : Finset S).image (vσ σ))
          rwa [hcimg σ] at this
      _ = (2*f)^S.card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
            nsmul_eq_mul, mul_pow]
          push_cast
          ring
  refine hbd.trans ?_
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_ge (by linarith) hf1
  rw [div_le_iff₀ (by norm_num)]
  exact_mod_cast (by omega : n ≤ S.card * 7)

