-- Prove2me | solution 1 for IntertempDUI.Finite.lemma_A1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-01T16:10:48.725183+00:00
-- url     : https://prove2.me/submissions/46ee5641-70da-4442-86de-c71e0a09cd5e

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

open IntertempDUI.Finite

namespace IDUIA1Counter

universe u

/-- The real line with the indiscrete topology (lifted to an arbitrary universe). -/
def Ind : Type u := ULift.{u} ℝ

instance : TopologicalSpace Ind := ⊤

instance : IndiscreteTopology Ind := ⟨rfl⟩

instance : Nonempty Ind := ⟨ULift.up 0⟩

instance : ConnectedSpace Ind where
  isPreconnected_univ := by
    intro U V hU hV _ hUi hVi
    rcases (TopologicalSpace.isOpen_top_iff U).1 hU with rfl | rfl
    · simp at hUi
    rcases (TopologicalSpace.isOpen_top_iff V).1 hV with rfl | rfl
    · simp at hVi
    simpa using hUi
  toNonempty := inferInstance

def v (x : Ind) : ℝ := ULift.down x

def mk (r : ℝ) : Ind := ULift.up r

lemma zero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
lemma one_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩

noncomputable def pt (I : Set (Time 1)) : Time 1 := by
  classical
  exact if h : ∃ t ∈ I, 0 < t.1 ∧ t.1 < 1 then h.choose else ⟨0, zero_mem⟩

lemma pt_spec (I : Set (Time 1)) (h : ∃ t ∈ I, 0 < t.1 ∧ t.1 < 1) :
    pt I ∈ I ∧ 0 < (pt I).1 ∧ (pt I).1 < 1 := by
  classical
  unfold pt
  rw [dif_pos h]
  exact h.choose_spec

noncomputable def pref : Pref 1 Ind := fun I a b => v (b (pt I)) ≤ v (a (pt I))

def A : Set (Traj 1 Ind) := {f | f ⟨0, zero_mem⟩ = f ⟨1, one_mem⟩}

lemma hconst : ∀ x : Ind, ContinuousMap.const (Time 1) x ∈ A := by
  intro x; simp [A]

/-- Every time interval contains a point strictly inside `(0,1)`. -/
lemma interval_inner (I : Set (Time 1)) (hI : IsTimeInterval I) :
    ∃ t ∈ I, 0 < t.1 ∧ t.1 < 1 := by
  obtain ⟨r, s, hr, hrs, hs, rfl⟩ := hI
  refine ⟨⟨(r + s) / 2, by linarith, by linarith⟩, ?_, ?_, ?_⟩
  · simp only [bracket, Set.mem_ofPred_eq]
    constructor
    · left; linarith
    · left; linarith
  · simp only; linarith
  · simp only; linarith

lemma hstd : Standing A pref := by
  intro I hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a _ b _
    exact le_total _ _
  · intro a _ b _ c _ h1 h2
    exact le_trans h2 h1
  · refine ⟨ContinuousMap.const _ (mk 1), hconst _, ContinuousMap.const _ (mk 0), hconst _, ?_⟩
    change (0:ℝ) ≤ 1 ∧ ¬ (1:ℝ) ≤ 0
    norm_num
  · intro a _ b _ a' _ b' _ ha hb
    obtain ⟨hm, -⟩ := pt_spec I (interval_inner I hI)
    simp only [pref]
    rw [ha hm, hb hm]

lemma not_richness : ¬ Richness A pref := by
  intro hR
  obtain ⟨f, hfA, hfa, -, hfc⟩ := hR 0 (1/3) (2/3) 1 (le_refl _) (by norm_num) (by norm_num)
    (by norm_num) (le_refl _)
    (ContinuousMap.const _ (mk 0)) (hconst _) (ContinuousMap.const _ (mk 0)) (hconst _)
    (ContinuousMap.const _ (mk 1)) (hconst _)
  have h0 : (⟨0, zero_mem⟩ : Time 1) ∈ bracket 1 0 (1/3) := by
    simp only [bracket, Set.mem_ofPred_eq]; norm_num
  have h1 : (⟨1, one_mem⟩ : Time 1) ∈ bracket 1 (2/3) 1 := by
    simp only [bracket, Set.mem_ofPred_eq]; norm_num
  have e0 := hfa h0
  have e1 := hfc h1
  have : f ⟨0, zero_mem⟩ = f ⟨1, one_mem⟩ := hfA
  rw [e0, e1] at this
  have h2 := congrArg v this
  change (0:ℝ) = 1 at h2
  norm_num at h2

lemma richnessStar : RichnessStar A pref := by
  classical
  intro Q R _ hRs hQR a ha b _
  let g : Time 1 → Ind := fun t => if t ∈ R ∧ 0 < t.1 ∧ t.1 < 1 then b t else a t
  have gc : Continuous g := continuous_top
  let f : Traj 1 Ind := ⟨g, gc⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · show g _ = g _
    simp only [g]
    rw [if_neg (by norm_num), if_neg (by norm_num)]
    exact ha
  · intro t ht
    show g t = a t
    simp only [g]
    rw [if_neg]
    rintro ⟨htR, -⟩
    exact Set.disjoint_left.1 hQR ht htR
  · intro I hIc
    obtain ⟨t0, ht0, rfl⟩ := hIc
    obtain ⟨N, s, t, hst, _, hReq⟩ := hRs
    have ht0' := ht0
    rw [hReq, Set.mem_iUnion] at ht0'
    obtain ⟨i, hi⟩ := ht0'
    obtain ⟨hs0, hst', ht1⟩ := hst i
    set m : ℝ := (s i + t i) / 2 with hm
    have hm0 : 0 < m := by rw [hm]; linarith
    have hm1 : m < 1 := by rw [hm]; linarith
    have hm01 : m ∈ Set.Icc (0:ℝ) 1 := ⟨hm0.le, hm1.le⟩
    -- the segment between t0 and m lies in the bracket, hence in R
    let P : Set (Time 1) := Set.projIcc (0:ℝ) 1 zero_le_one '' Set.uIcc t0.1 m
    have hPc : IsPreconnected P :=
      isPreconnected_uIcc.image _ continuous_projIcc.continuousOn
    have ht0P : t0 ∈ P := ⟨t0.1, Set.left_mem_uIcc, Set.projIcc_val _ _⟩
    have hmP : (⟨m, hm01⟩ : Time 1) ∈ P := ⟨m, Set.right_mem_uIcc, Set.projIcc_of_mem _ hm01⟩
    have hPR : P ⊆ R := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Set.Icc (0:ℝ) 1 := by
        rcases Set.mem_uIcc.1 hx with h | h
        · exact ⟨le_trans t0.2.1 h.1, le_trans h.2 hm1.le⟩
        · exact ⟨le_trans hm0.le h.1, le_trans h.2 t0.2.2⟩
      rw [Set.projIcc_of_mem _ hx', hReq, Set.mem_iUnion]
      refine ⟨i, ?_⟩
      simp only [bracket, Set.mem_ofPred_eq] at hi ⊢
      obtain ⟨hi1, hi2⟩ := hi
      rcases Set.mem_uIcc.1 hx with h | h
      · constructor
        · by_cases hxs : s i < x
          · exact Or.inl hxs
          · rcases hi1 with h' | h'
            · exact absurd (lt_of_lt_of_le h' h.1) hxs
            · right; refine ⟨h'.1, ?_⟩; have := t0.2.1; linarith [h.1, h'.2]
        · left; rw [hm] at h; linarith [h.2]
      · constructor
        · left; rw [hm] at h; linarith [h.1]
        · by_cases hxs : x < t i
          · exact Or.inl hxs
          · rcases hi2 with h' | h'
            · exact absurd (lt_of_le_of_lt h.2 h') hxs
            · right; refine ⟨h'.1, ?_⟩; have := t0.2.2; linarith [h.2, h'.2]
    have hsub : P ⊆ connectedComponentIn R t0 := hPc.subset_connectedComponentIn ht0P hPR
    have hex : ∃ t ∈ connectedComponentIn R t0, 0 < t.1 ∧ t.1 < 1 :=
      ⟨⟨m, hm01⟩, hsub hmP, hm0, hm1⟩
    obtain ⟨hpI, hp0, hp1⟩ := pt_spec _ hex
    have hpR : pt (connectedComponentIn R t0) ∈ R := connectedComponentIn_subset _ _ hpI
    have hfe : f (pt (connectedComponentIn R t0)) = b (pt (connectedComponentIn R t0)) := by
      show g _ = _
      simp only [g]
      rw [if_pos ⟨hpR, hp0, hp1⟩]
    simp only [indiff, pref]
    rw [hfe]
    exact ⟨le_refl _, le_refl _⟩

end IDUIA1Counter

open IDUIA1Counter in
theorem solution : ¬ (∀ {X : Type} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref),
    RichnessStar A pref ↔ Richness A pref) := by
  intro h
  exact not_richness ((h (X := Ind.{0}) 1 one_pos A hconst pref hstd).1 richnessStar)
