-- Prove2me | solution 1 for IsRandomnessNecessaryADA.Plain.Supplement.theorem_1_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T18:20:54.326312+00:00
-- url     : https://prove2.me/submissions/53f123f3-7179-47f6-9086-b17a3ccd2f4c

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Survivors
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Tables
import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_ConditionalCube
import Theorems.Thm_IsRandomnessNecessaryADA_Plain_lemma_4_2
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Supplement_SeedProtocol
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44
import Theorems.Thm_IsRandomnessNecessaryADA_Plain_lemma_4_1
section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L35

open IsRandomnessNecessaryADA.Plain

end IsRandomnessNecessaryADA.Plain.Dev.L35

namespace IsRandomnessNecessaryADA.Plain.Dev.L35

open IsRandomnessNecessaryADA.Plain

theorem replay_append {X Q : Type} {n : ℕ} (m : Response X Q n) (s : Fin n → X) (h : List Q) (q : Q) :
    replayQueries m s (h ++ [q]) = replayQueries m s h ++ [(q, m s (replayQueries m s h) q)] := by
  simp [replayQueries, List.foldl_append]

theorem consistent_prefix {X : Type} {n : ℕ} (m : Mechanism X n) (s : Fin n → X)
    (T : Transcript (StatisticalQuery X)) (q : StatisticalQuery X) (a : ℝ)
    (h : Consistent m s (T ++ [(q, a)])) : Consistent m s T ∧ m s T q = a := by
  unfold Consistent at h ⊢
  simp only [List.map_append, List.map_cons, List.map_nil] at h
  rw [replay_append] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  refine ⟨h1, ?_⟩
  rw [h1] at h2
  simpa using (Prod.mk.inj (List.cons.inj h2).1).2

end IsRandomnessNecessaryADA.Plain.Dev.L35

namespace IsRandomnessNecessaryADA.Plain

end IsRandomnessNecessaryADA.Plain
end

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L12

open IsRandomnessNecessaryADA.Plain

theorem mean_gen {N : ℕ} (hN : 0 < N) {X : Type} [Fintype X] (e : Fin N ↪ X) (Q : BooleanQuery X) :
    populationMean (uniformSupport hN e) (liftQuery Q) = (∑ i, bitValue (Q (e i))) / N := by
  classical
  unfold populationMean uniformSupport
  have hp : ∀ i, ((uniformFin N hN) i).toReal = 1 / (N : ℝ) := by
    intro i
    unfold uniformFin
    simp [PMF.uniformOfFintype_apply]
  have hmap : ∀ x : X, ((PMF.map e (uniformFin N hN)) x).toReal =
      ∑ i : Fin N, if x = e i then 1 / (N : ℝ) else 0 := by
    intro x
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : x = e i
      · simp [h, hp]
      · simp [h]
    · intro i _
      split_ifs
      · exact PMF.apply_ne_top _ _
      · simp
  simp only [hmap, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, ∑ x : X, (if x = e i then 1 / (N : ℝ) else 0) *
      (liftQuery Q x).val = 1 / (N : ℝ) * bitValue (Q (e i)) := by
    intro i
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp [liftQuery]
  simp only [this]
  rw [← Finset.mul_sum]
  field_simp

theorem bitSum_pattern {N : ℕ} (v : BooleanQuery (Fin N)) :
    ∑ i, bitValue (v i) = ((Finset.univ.filter (fun i => v i = true)).card : ℝ) := by
  classical
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  cases v i <;> simp [bitValue]

end IsRandomnessNecessaryADA.Plain.Dev.L12
end

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L12

section Abstract

variable {S Q : Type} [Fintype S] [Fintype Q] [Nonempty Q]

/-- deterministic run from a starting transcript, first-step form -/
def detRun (mech : S → List (Q × ℝ) → Q → ℝ) (A : List (Q × ℝ) → Q) (s : S) :
    List (Q × ℝ) → ℕ → List (Q × ℝ)
  | T0, 0 => T0
  | T0, j + 1 => detRun mech A s (T0 ++ [(A T0, mech s T0 (A T0))]) j

/-- randomized run from a starting transcript, first-step form -/
noncomputable def randRun (mech : S → List (Q × ℝ) → Q → ℝ) (ρ : List (Q × ℝ) → PMF Q) (s : S) :
    List (Q × ℝ) → ℕ → PMF (List (Q × ℝ))
  | T0, 0 => PMF.pure T0
  | T0, j + 1 => (ρ T0).bind (fun q => randRun mech ρ s (T0 ++ [(q, mech s T0 q)]) j)

theorem detRun_congr (mech : S → List (Q × ℝ) → Q → ℝ) (A A' : List (Q × ℝ) → Q) (s : S) (j : ℕ) :
    ∀ T1 : List (Q × ℝ), (∀ T, T1 <+: T → A T = A' T) → detRun mech A s T1 j = detRun mech A' s T1 j := by
  induction j with
  | zero => intro T1 _; rfl
  | succ j ih =>
    intro T1 h
    simp only [detRun]
    have h1 : A T1 = A' T1 := h T1 (List.prefix_refl _)
    rw [h1]
    refine ih _ (fun T hT => h T ?_)
    exact (List.prefix_append _ _).trans hT


theorem randRun_last (mech : S → List (Q × ℝ) → Q → ℝ) (ρ : List (Q × ℝ) → PMF Q) (s : S) (j : ℕ) :
    ∀ T0 : List (Q × ℝ), randRun mech ρ s T0 (j + 1) =
      (randRun mech ρ s T0 j).bind (fun T => (ρ T).map (fun q => T ++ [(q, mech s T q)])) := by
  induction j with
  | zero =>
    intro T0
    simp only [randRun]
    rw [PMF.pure_bind]
    exact (PMF.bind_pure_comp _ _).symm.trans rfl |>.trans (by rfl)
  | succ j ih =>
    intro T0
    conv_lhs => rw [randRun]
    conv_rhs => rw [randRun]
    rw [PMF.bind_bind]
    congr 1
    funext q
    exact ih _

open scoped Classical in
theorem derand (mech : S → List (Q × ℝ) → Q → ℝ) (cons : S → List (Q × ℝ) → Prop)
    (hcons : ∀ s T q a, cons s (T ++ [(q, a)]) ↔ cons s T ∧ mech s T q = a)
    (w : S → ℝ) (hw : ∀ s, 0 ≤ w s) (bad : List (Q × ℝ) → Prop) :
    ∀ (j : ℕ) (ρ : List (Q × ℝ) → PMF Q) (T0 : List (Q × ℝ)),
      ∃ A : List (Q × ℝ) → Q,
        ∑ s, w s * (if cons s T0 then
            ((randRun mech ρ s T0 j).toOuterMeasure {T | bad T}).toReal else 0) ≤
          ∑ s, w s * (if cons s T0 ∧ bad (detRun mech A s T0 j) then 1 else 0) := by
  intro j
  induction j with
  | zero =>
    intro ρ T0
    refine ⟨fun _ => Classical.arbitrary Q, le_of_eq ?_⟩
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [randRun, detRun, PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq]
    by_cases hc : cons s T0 <;> by_cases hb : bad T0 <;> simp [hc, hb]
  | succ j ih =>
    intro ρ T0
    set E : Set (List (Q × ℝ)) := {T | bad T} with hE
    let P : S → List (Q × ℝ) → ℝ := fun s T1 => ((randRun mech ρ s T1 j).toOuterMeasure E).toReal
    let valR : List (Q × ℝ) → ℝ := fun T1 => ∑ s, w s * (if cons s T1 then P s T1 else 0)
    let valD : (List (Q × ℝ) → Q) → List (Q × ℝ) → ℝ := fun A T1 =>
      ∑ s, w s * (if cons s T1 ∧ bad (detRun mech A s T1 j) then 1 else 0)
    have ih' : ∀ (q : Q) (a : ℝ), ∃ A', valR (T0 ++ [(q, a)]) ≤ valD A' (T0 ++ [(q, a)]) :=
      fun q a => ih ρ _
    choose Aq hAq using ih'
    let Ans : Q → Finset ℝ := fun q => Finset.univ.image (fun s => mech s T0 q)
    have hstep : ∀ s, ((randRun mech ρ s T0 (j + 1)).toOuterMeasure E).toReal =
        ∑ q, (ρ T0 q).toReal * P s (T0 ++ [(q, mech s T0 q)]) := by
      intro s
      simp only [randRun]
      rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [ENNReal.toReal_mul]
      · intro q _
        refine ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ?_
        refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        rw [PMF.toOuterMeasure_apply]
        calc ∑' x, E.indicator (randRun mech ρ s (T0 ++ [(q, mech s T0 q)]) j) x
            ≤ ∑' x, (randRun mech ρ s (T0 ++ [(q, mech s T0 q)]) j) x :=
              ENNReal.tsum_le_tsum (fun x => Set.indicator_le_self _ _ x)
          _ = 1 := PMF.tsum_coe _
    have hsplit : ∀ q, ∑ s, w s * (if cons s T0 then P s (T0 ++ [(q, mech s T0 q)]) else 0) =
        ∑ a ∈ Ans q, valR (T0 ++ [(q, a)]) := by
      intro q
      simp only [valR, hcons]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      have hmem : mech s T0 q ∈ Ans q := Finset.mem_image.2 ⟨s, Finset.mem_univ _, rfl⟩
      have : ∀ a ∈ Ans q, w s * (if cons s T0 ∧ mech s T0 q = a then P s (T0 ++ [(q, a)]) else 0) =
          if a = mech s T0 q then w s * (if cons s T0 then P s (T0 ++ [(q, mech s T0 q)]) else 0)
            else 0 := by
        intro a _
        by_cases hc : cons s T0
        · by_cases ha : a = mech s T0 q
          · subst ha; simp [hc]
          · simp [hc, ha, Ne.symm ha]
        · simp [hc]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Ans q), if_pos hmem]
    have hval : valR T0 ≥ 0 ∨ True := Or.inr trivial
    let G : Q → ℝ := fun q => ∑ a ∈ Ans q, valD (Aq q a) (T0 ++ [(q, a)])
    have hρ1 : ∑ q, (ρ T0 q).toReal = 1 := by
      rw [← ENNReal.toReal_sum (fun q _ => PMF.apply_ne_top _ _)]
      have : ∑ q, ρ T0 q = 1 := by have := (ρ T0).tsum_coe; rwa [tsum_fintype] at this
      rw [this]; simp
    obtain ⟨qs, _, hqs⟩ := Finset.exists_max_image Finset.univ G ⟨Classical.arbitrary Q, Finset.mem_univ _⟩
    let A : List (Q × ℝ) → Q := fun T =>
      if T = T0 then qs else
        if h : ∃ a, T0 ++ [(qs, a)] <+: T then Aq qs (Classical.choose h) T else qs
    refine ⟨A, ?_⟩
    have hLHS : ∑ s, w s * (if cons s T0 then
        ((randRun mech ρ s T0 (j + 1)).toOuterMeasure E).toReal else 0) ≤ G qs := by
      calc _ = ∑ s, ∑ q, (ρ T0 q).toReal * (w s * (if cons s T0 then
              P s (T0 ++ [(q, mech s T0 q)]) else 0)) := by
            refine Finset.sum_congr rfl (fun s _ => ?_)
            by_cases hc : cons s T0
            · simp only [hc, if_true, hstep s, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun q _ => by ring)
            · simp [hc]
        _ = ∑ q, (ρ T0 q).toReal * ∑ s, w s * (if cons s T0 then
              P s (T0 ++ [(q, mech s T0 q)]) else 0) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun q _ => by rw [Finset.mul_sum])
        _ = ∑ q, (ρ T0 q).toReal * ∑ a ∈ Ans q, valR (T0 ++ [(q, a)]) := by
            simp only [hsplit]
        _ ≤ ∑ q, (ρ T0 q).toReal * G q := by
            refine Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
            exact Finset.sum_le_sum (fun a _ => hAq q a)
        _ ≤ ∑ q, (ρ T0 q).toReal * G qs :=
            Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hqs q (Finset.mem_univ _))
              ENNReal.toReal_nonneg)
        _ = G qs := by rw [← Finset.sum_mul, hρ1, one_mul]
    refine hLHS.trans (le_of_eq ?_)
    have hAT0 : A T0 = qs := by simp [A]
    have hagree : ∀ a : ℝ, ∀ T, (T0 ++ [(qs, a)]) <+: T → A T = Aq qs a T := by
      intro a T hT
      have hne : T ≠ T0 := by
        rintro rfl
        have := hT.length_le
        simp at this
      have hex : ∃ a', T0 ++ [(qs, a')] <+: T := ⟨a, hT⟩
      have hchoose := Classical.choose_spec hex
      have : Classical.choose hex = a := by
        have h2 := List.IsPrefix.eq_of_length (List.prefix_of_prefix_length_le hchoose hT (by simp)) (by simp)
        have h3 := List.append_cancel_left h2
        exact (Prod.mk.inj (List.cons.inj h3).1).2
      simp only [A, if_neg hne, dif_pos hex, this]
    have hrun : ∀ s, detRun mech A s T0 (j + 1) =
        detRun mech (Aq qs (mech s T0 qs)) s (T0 ++ [(qs, mech s T0 qs)]) j := by
      intro s
      simp only [detRun, hAT0]
      exact detRun_congr mech A _ s j _ (fun T hT => hagree _ T hT)
    show G qs = ∑ s, w s * (if cons s T0 ∧ bad (detRun mech A s T0 (j + 1)) then 1 else 0)
    simp only [hrun]
    simp only [G, valD]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have hmem : mech s T0 qs ∈ Ans qs := Finset.mem_image.2 ⟨s, Finset.mem_univ _, rfl⟩
    have : ∀ a ∈ Ans qs, w s * (if cons s (T0 ++ [(qs, a)]) ∧
        bad (detRun mech (Aq qs a) s (T0 ++ [(qs, a)]) j) then 1 else 0) =
        if a = mech s T0 qs then w s * (if cons s T0 ∧
          bad (detRun mech (Aq qs (mech s T0 qs)) s (T0 ++ [(qs, mech s T0 qs)]) j) then 1 else 0)
        else 0 := by
      intro a _
      by_cases ha : a = mech s T0 qs
      · subst ha; simp [hcons]
      · simp [hcons, ha, Ne.symm ha]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Ans qs), if_pos hmem]

end Abstract


end IsRandomnessNecessaryADA.Plain.Dev.L12
end

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L41

open IsRandomnessNecessaryADA.Plain


section Decomp

variable {N M : ℕ} (i : Fin N)

end Decomp


section Decomp2

variable {N M : ℕ} (i : Fin N)

end Decomp2


end IsRandomnessNecessaryADA.Plain.Dev.L41
end

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L41

end IsRandomnessNecessaryADA.Plain.Dev.L41
end

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L41

open IsRandomnessNecessaryADA.Plain

end IsRandomnessNecessaryADA.Plain.Dev.L41
end

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain

end IsRandomnessNecessaryADA.Plain
end

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L12

open IsRandomnessNecessaryADA.Plain

section Defs

variable {n M : ℕ}

abbrev Tr (n M : ℕ) := List (Table (20 * n) M × ℝ)

noncomputable def lt (T : Tr n M) : Transcript (StatisticalQuery (Fin (20 * n) × Fin M)) :=
  T.map (fun qa => (liftQuery qa.1, qa.2))

noncomputable def mkPath {N : ℕ} (C : Finset (Fin N)) : ThresholdPath N where
  common := C
  length := (Cᶜ).card
  change := ((Cᶜ).orderEmbOfFin rfl).toEmbedding
  complement i := by
    constructor
    · intro hi t ht
      have := Finset.orderEmbOfFin_mem (Cᶜ) rfl t
      simp only [RelEmbedding.coe_toEmbedding] at ht
      rw [ht] at this
      simp [hi] at this
    · intro h
      by_contra hi
      have : i ∈ (↑(Cᶜ) : Set (Fin N)) := by simpa using hi
      rw [← Finset.range_orderEmbOfFin (Cᶜ) rfl] at this
      obtain ⟨t, ht⟩ := this
      exact h t (by simpa using ht)

end Defs


section Proc

variable {n M : ℕ}
variable (Kc : ∀ (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (p : ThresholdPath (20 * n)),
  PMF (Fin (p.length + 1) → Table (20 * n) M))


theorem supp_pattern {N M : ℕ} (K : PMF (Table N M)) (r : Locations N M) (v : BooleanQuery (Fin N))
    (hK : K = completionLaw r v) (Q : Table N M) (hQ : Q ∈ K.support) (x : Fin N × Fin M)
    (hx : x.2 = r x.1) : Q x = v x.1 := by
  subst hK
  unfold completionLaw tableLaw at hQ
  rw [PMF.support_map] at hQ
  obtain ⟨q, _, rfl⟩ := hQ
  simp [completeTable, hx]

end Proc


end IsRandomnessNecessaryADA.Plain.Dev.L12
end

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L12

open IsRandomnessNecessaryADA.Plain

section Dens

variable {n M : ℕ}
variable (Kc : ∀ (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (p : ThresholdPath (20 * n)),
  PMF (Fin (p.length + 1) → Table (20 * n) M))


theorem map_apply_le {α β : Type} [Fintype α] (ρ : PMF α) (g : α → β) (hg : Function.Injective g)
    (c : ENNReal) (hc : ∀ q, ρ q ≤ c) (y : β) : (ρ.map g) y ≤ c := by
  classical
  by_cases hy : ∃ q, g q = y
  · obtain ⟨q, rfl⟩ := hy
    rw [PMF.map_apply, tsum_eq_single q]
    · simpa using hc q
    · intro q' hq'
      have : g q ≠ g q' := fun h => hq' (hg h).symm
      simp [this]
  · push Not at hy
    rw [PMF.map_apply]
    simp [fun q => (hy q).symm]

end Dens


end IsRandomnessNecessaryADA.Plain.Dev.L12
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
/-- single-round failure bound of Lemma 4.1 for N rows and sample size n' -/
noncomputable def epsG (N n' M : ℕ) : ℝ :=
  (N : ℝ) * (2 : ℝ) ^ (N - 1) * Real.sqrt (2 * (N : ℝ) ^ n' / M)

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartG
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
theorem tom_compl {α : Type} (K : PMF α) (P : α → Prop) :
    (K.toOuterMeasure {Q | ¬ P Q}).toReal = 1 - (K.toOuterMeasure {Q | P Q}).toReal := by
  have hsum : K.toOuterMeasure {Q | P Q} + K.toOuterMeasure {Q | ¬ P Q} = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    have : {Q | ¬ P Q} = {Q | P Q}ᶜ := rfl
    rw [this]
    simp only [Set.indicator_self_add_compl_apply]
    exact K.tsum_coe
  have h1 : K.toOuterMeasure {Q | P Q} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (hsum ▸ le_self_add)
  have h2 : K.toOuterMeasure {Q | ¬ P Q} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (hsum ▸ le_add_self)
  have := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add h1 h2] at this
  simp at this
  linarith

theorem tom_le_one {α : Type} (K : PMF α) (s : Set α) : (K.toOuterMeasure s).toReal ≤ 1 := by
  have : K.toOuterMeasure s ≤ 1 := by
    rw [PMF.toOuterMeasure_apply]
    calc ∑' x, s.indicator K x ≤ ∑' x, K x := ENNReal.tsum_le_tsum (fun x => Set.indicator_le_self _ _ x)
      _ = 1 := K.tsum_coe
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

open scoped Classical in
theorem bind_prob {L : Type} [Fintype L] [Nonempty L] {β : L → Type} (K : (r : L) → PMF (β r))
    (P : (r : L) → β r → Prop) :
    probability ((PMF.uniformOfFintype L).bind (fun r => (K r).map (fun Q => decide (P r Q)))) {true} =
      (1 / (Fintype.card L : ℝ)) * ∑ r, ((K r).toOuterMeasure {Q | P r Q}).toReal := by
  unfold probability
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [PMF.toOuterMeasure_map_apply, ENNReal.toReal_mul, PMF.uniformOfFintype_apply]
    have : (fun Q => decide (P r Q)) ⁻¹' {true} = {Q | P r Q} := by
      ext Q; simp
    rw [this]
    simp
  · intro r _
    refine ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ?_
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [PMF.toOuterMeasure_apply]
    calc ∑' x, _ ≤ ∑' x, ((K r).map (fun Q => decide (P r Q))) x :=
          ENNReal.tsum_le_tsum (fun x => Set.indicator_le_self _ _ x)
      _ = 1 := PMF.tsum_coe _

theorem near_opt_gen (N M n' : ℕ) [NeZero M] (hN : 0 < N)
    (m : Mechanism (Fin N × Fin M) n') (δ : ℝ) (hδ : 0 < δ) :
    ∃ Kc : ∀ (r : Locations N M) (h : List (Table N M)) (p : ThresholdPath N),
        PMF (Fin (p.length + 1) → Table N M),
      (∀ r h p j, (Kc r h p).map (fun Q => Q j) = completionLaw r (thresholdPattern p j)) ∧
      ∀ (h : List (Table N M)) (path : Locations N M → ThresholdPath N),
        ∑ r, ((Kc r h (path r)).toOuterMeasure
            {Q | ¬ profilesAgree m r h (path r) Q}).toReal ≤
          (Fintype.card (Locations N M) : ℝ) * (epsG N n' M + δ) := by
  classical
  let Val : (r : Locations N M) → (h : List (Table N M)) → (p : ThresholdPath N) →
      Set ℝ := fun r h p =>
    {x | ∃ K : PMF (Fin (p.length + 1) → Table N M),
      (∀ j, K.map (fun Q => Q j) = completionLaw r (thresholdPattern p j)) ∧
      x = (K.toOuterMeasure {Q | profilesAgree m r h p Q}).toReal}
  have hne : ∀ r h p, (Val r h p).Nonempty := by
    intro r h p
    obtain ⟨K, hK, _⟩ := lemma_4_1 N M n' hN m h (fun _ => p)
    exact ⟨_, K r, hK r, rfl⟩
  have hbdd : ∀ r h p, BddAbove (Val r h p) := by
    intro r h p
    refine ⟨1, ?_⟩
    rintro x ⟨K, _, rfl⟩
    exact tom_le_one _ _
  have hex : ∀ r h p, ∃ K : PMF (Fin (p.length + 1) → Table N M),
      (∀ j, K.map (fun Q => Q j) = completionLaw r (thresholdPattern p j)) ∧
      sSup (Val r h p) - δ < (K.toOuterMeasure {Q | profilesAgree m r h p Q}).toReal := by
    intro r h p
    obtain ⟨x, ⟨K, hK, rfl⟩, hx⟩ := exists_lt_of_lt_csSup (hne r h p) (by linarith : sSup (Val r h p) - δ < sSup (Val r h p))
    exact ⟨K, hK, hx⟩
  choose Kc hKm hKv using hex
  refine ⟨Kc, hKm, ?_⟩
  intro h path
  obtain ⟨K', hK'm, hK'b⟩ := lemma_4_1 N M n' hN m h path
  rw [bind_prob K' (fun r Q => profilesAgree m r h (path r) Q)] at hK'b
  have hcard : (0 : ℝ) < Fintype.card (Locations N M) := by exact_mod_cast Fintype.card_pos
  have hcmp : ∀ r, (((K' r).toOuterMeasure {Q | profilesAgree m r h (path r) Q}).toReal) <
      ((Kc r h (path r)).toOuterMeasure {Q | profilesAgree m r h (path r) Q}).toReal + δ := by
    intro r
    have h1 : ((K' r).toOuterMeasure {Q | profilesAgree m r h (path r) Q}).toReal ≤ sSup (Val r h (path r)) :=
      le_csSup (hbdd _ _ _) ⟨K' r, hK'm r, rfl⟩
    have h2 := hKv r h (path r)
    linarith
  simp only [tom_compl]
  have hsum : ∑ r, ((K' r).toOuterMeasure {Q | profilesAgree m r h (path r) Q}).toReal ≤
      ∑ r, (((Kc r h (path r)).toOuterMeasure {Q | profilesAgree m r h (path r) Q}).toReal + δ) :=
    Finset.sum_le_sum (fun r _ => (hcmp r).le)
  rw [Finset.sum_add_distrib] at hsum
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum ⊢
  have hε : 1 - epsG N n' M ≤ (1 / (Fintype.card (Locations N M) : ℝ)) *
      ∑ r, ((K' r).toOuterMeasure {Q | profilesAgree m r h (path r) Q}).toReal := by
    unfold epsG; exact hK'b
  have hε' : (Fintype.card (Locations N M) : ℝ) * (1 - epsG N n' M) ≤
      ∑ r, ((K' r).toOuterMeasure {Q | profilesAgree m r h (path r) Q}).toReal := by
    have := mul_le_mul_of_nonneg_left hε hcard.le
    rwa [← mul_assoc, mul_one_div_cancel hcard.ne', one_mul] at this
  nlinarith

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartG
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
alias near_opt_gen := IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartG.near_opt_gen

abbrev Cand (n b : ℕ) := (Fin n → Fin (20 * n)) × PrivateSeed b

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {n M b : ℕ}
/-- the seed mechanism as a plain mechanism with b extra sample points; the parity of the
row of extra point t is seed bit t -/
noncomputable def encode (m : SeedMechanism (Fin (20 * n) × Fin M) n b) :
    Mechanism (Fin (20 * n) × Fin M) (n + b) :=
  fun S T q => m (fun t => decide ((S (Fin.natAdd n t)).1.val % 2 = 0))
    (fun t => S (Fin.castAdd b t)) T q

noncomputable def mechS (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (r : Locations (20 * n) M)
    (c : Cand n b) (T : Tr n M) (q : Table (20 * n) M) : ℝ :=
  m c.2 (fun t => supportEmbedding r (c.1 t)) (lt T) (liftQuery q)

def consS (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (r : Locations (20 * n) M)
    (c : Cand n b) (T : Tr n M) : Prop :=
  Consistent (m c.2) (fun t => supportEmbedding r (c.1 t)) (lt T)

noncomputable def survS (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (r : Locations (20 * n) M)
    (T : Tr n M) : Finset (Cand n b) := by
  classical
  exact Finset.univ.filter (fun c => consS m r c T)

noncomputable def commonS (H : Finset (Cand n b)) : Finset (Fin (20 * n)) := by
  classical
  exact Finset.univ.filter (fun i =>
    (8 / 10 : ℝ) * H.card ≤ (H.filter (fun c => ∃ t, c.1 t = i)).card)

noncomputable def pathS (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (r : Locations (20 * n) M)
    (T : Tr n M) : ThresholdPath (20 * n) :=
  mkPath (commonS (survS m r T))

noncomputable def SepS (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (T : Tr n M) (Q : Table (20 * n) M) : Prop :=
  ∀ a : ℝ, |a - populationMean (uniformSupport hN (supportEmbedding r)) (liftQuery Q)| ≤ 1 / 10 →
    ((((survS m r T).filter (fun c => mechS m r c T Q = a)).card : ℕ) : ℝ) ≤
      (9 / 10 : ℝ) * (survS m r T).card

open scoped Classical in
noncomputable def selS (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (T : Tr n M) (p : ThresholdPath (20 * n))
    (Θ : Fin (p.length + 1) → Table (20 * n) M) : Fin (p.length + 1) :=
  if hex : ∃ ℓ, SepS hN m r T (Θ ℓ) then Classical.choose hex else 0

/-- exact horizon for 2^b N^n candidates -/
noncomputable def horizonS (n b : ℕ) : ℕ :=
  Nat.ceil (Real.log ((2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n) / Real.log (10 / 9 : ℝ)) + 1

noncomputable def columnCountS (n b : ℕ) : ℕ :=
  2 * (20 * n) ^ (n + b) *
    (100 * horizonS n b * (20 * n) * 2 ^ (20 * n) * densityFactor (20 * n) ^ horizonS n b) ^ 2

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {n M b : ℕ}
variable (Kc : ∀ (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (p : ThresholdPath (20 * n)),
  PMF (Fin (p.length + 1) → Table (20 * n) M))
noncomputable def qlawS (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (T : Tr n M) : PMF (Table (20 * n) M) :=
  (Kc r (T.map Prod.fst) (pathS m r T)).map
    (fun Θ => Θ (selS hN m r T (pathS m r T) Θ))

open scoped Classical in
noncomputable def stepS (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (c : Cand n b) (x : Tr n M × Bool) : PMF (Tr n M × Bool) :=
  (Kc r (x.1.map Prod.fst) (pathS m r x.1)).map (fun Θ =>
    (x.1 ++ [(Θ (selS hN m r x.1 (pathS m r x.1) Θ),
        mechS m r c x.1 (Θ (selS hN m r x.1 (pathS m r x.1) Θ)))],
      x.2 || decide (¬ profilesAgree (encode m) r (x.1.map Prod.fst) (pathS m r x.1) Θ)))

noncomputable def fwS (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (c : Cand n b) : ℕ → PMF (Tr n M × Bool)
  | 0 => PMF.pure ([], false)
  | j + 1 => (fwS hN m r c j).bind (stepS Kc hN m r c)

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
  IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {n M b : ℕ}
theorem consS_snoc (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (r : Locations (20 * n) M)
    (c : Cand n b) (T : Tr n M) (q : Table (20 * n) M) (a : ℝ) :
    consS m r c (T ++ [(q, a)]) ↔ consS m r c T ∧ mechS m r c T q = a := by
  unfold consS mechS
  constructor
  · intro h
    exact IsRandomnessNecessaryADA.Plain.Dev.L35.consistent_prefix (m c.2)
      (fun t => supportEmbedding r (c.1 t)) (lt T) (liftQuery q) a (by simpa [lt] using h)
  · rintro ⟨h1, h2⟩
    unfold Consistent at h1 ⊢
    simp only [lt, List.map_append, List.map_cons, List.map_nil] at h1 h2 ⊢
    rw [IsRandomnessNecessaryADA.Plain.Dev.L35.replay_append, h1, h2]

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {n M b : ℕ}
variable (Kc : ∀ (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (p : ThresholdPath (20 * n)),
  PMF (Fin (p.length + 1) → Table (20 * n) M))
alias consS_snoc := IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP.consS_snoc

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
  IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {n M b : ℕ}
theorem consS_nil (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (r : Locations (20 * n) M)
    (c : Cand n b) : consS m r c [] := by
  simp [consS, lt, Consistent, replayQueries]

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {n M b : ℕ}
variable (Kc : ∀ (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (p : ThresholdPath (20 * n)),
  PMF (Fin (p.length + 1) → Table (20 * n) M))
alias consS_nil := IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP.consS_nil

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
  IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {n M b : ℕ}
/-- double counting: each candidate has at most n distinct rows -/
theorem commonS_card (H : Finset (Cand n b)) :
    (8 / 10 : ℝ) * H.card * (commonS H).card ≤ n * H.card := by
  classical
  set C := commonS H with hC
  have h1 : ∀ i ∈ C, (8 / 10 : ℝ) * H.card ≤ ((H.filter (fun c => ∃ t, c.1 t = i)).card : ℝ) := by
    intro i hi
    have := (Finset.mem_filter.1 (by simpa [hC, commonS] using hi : i ∈ Finset.univ.filter
      (fun i => (8 / 10 : ℝ) * H.card ≤ (H.filter (fun c => ∃ t, c.1 t = i)).card))).2
    convert this
  have h2 : (C.card : ℝ) * ((8 / 10 : ℝ) * H.card) ≤
      ∑ i ∈ C, ((H.filter (fun c => ∃ t, c.1 t = i)).card : ℝ) := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ h1
  have h3 : ∑ i ∈ C, ((H.filter (fun c => ∃ t, c.1 t = i)).card : ℝ) =
      ∑ c ∈ H, ((C.filter (fun i => ∃ t, c.1 t = i)).card : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  have h4 : ∀ c ∈ H, ((C.filter (fun i => ∃ t, c.1 t = i)).card : ℝ) ≤ n := by
    intro c _
    have : C.filter (fun i => ∃ t, c.1 t = i) ⊆ Finset.univ.image c.1 := by
      intro i hi
      obtain ⟨t, ht⟩ := (Finset.mem_filter.1 hi).2
      exact Finset.mem_image.2 ⟨t, Finset.mem_univ _, ht⟩
    have h5 := (Finset.card_le_card this).trans (Finset.card_image_le (s := Finset.univ) (f := c.1))
    simp only [Finset.card_univ, Fintype.card_fin] at h5
    exact_mod_cast h5
  have h6 : ∑ c ∈ H, ((C.filter (fun i => ∃ t, c.1 t = i)).card : ℝ) ≤ ∑ c ∈ H, (n : ℝ) :=
    Finset.sum_le_sum h4
  simp only [Finset.sum_const, nsmul_eq_mul] at h6
  nlinarith

theorem horizonS_pos (n b : ℕ) (hn : 0 < n) :
    (2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n < (10 / 9 : ℝ) ^ (horizonS n b) := by
  have hl : 0 < Real.log (10 / 9 : ℝ) := Real.log_pos (by norm_num)
  have hNpos : (0 : ℝ) < ((20 * n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 20 * n by omega)
  have h1 : Real.log ((2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n) / Real.log (10 / 9 : ℝ) <
      (horizonS n b : ℝ) := by
    unfold horizonS
    have := Nat.le_ceil (Real.log ((2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n) / Real.log (10 / 9 : ℝ))
    push_cast at this ⊢
    linarith
  rw [div_lt_iff₀ hl] at h1
  have h2 : (10 / 9 : ℝ) ^ (horizonS n b) =
      Real.exp ((horizonS n b : ℝ) * Real.log (10 / 9 : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h2]
  calc (2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n =
        Real.exp (Real.log ((2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n)) :=
        (Real.exp_log (by positivity)).symm
    _ < _ := Real.exp_lt_exp.2 h1

theorem parity_row (hn : 0 < n) (i : Fin (20 * n)) (β : Bool) :
    ∃ j : Fin (20 * n), j ≠ i ∧ decide (j.val % 2 = 0) = β := by
  rcases β with _ | _
  · by_cases hi : i.val = 1
    · exact ⟨⟨3, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega,
        by simp⟩
    · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega,
        by simp⟩
  · by_cases hi : i.val = 0
    · exact ⟨⟨2, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega,
        by simp⟩
    · exact ⟨⟨0, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega,
        by simp⟩

/-- the response profile of `encode m` at the extended sample (s, rows encoding σ) is the
response bit of `m σ` on s -/
theorem bit_agree (hn : 0 < n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (i : Fin (20 * n))
    (Q1 Q2 : Table (20 * n) M)
    (hprof : responseProfile (encode m) r h i Q1 = responseProfile (encode m) r h i Q2)
    (c : Cand n b) (hav : ∀ t, c.1 t ≠ i) :
    responseBit (m c.2 (fun t => supportEmbedding r (c.1 t))
        (replayQueries (m c.2) (fun t => supportEmbedding r (c.1 t)) (h.map liftQuery))
        (liftQuery Q1)) =
      responseBit (m c.2 (fun t => supportEmbedding r (c.1 t))
        (replayQueries (m c.2) (fun t => supportEmbedding r (c.1 t)) (h.map liftQuery))
        (liftQuery Q2)) := by
  choose ρ hρ1 hρ2 using fun u : Fin b => parity_row hn i (c.2 u)
  set s' : Fin (n + b) → {j : Fin (20 * n) // j ≠ i} :=
    Fin.append (fun t => ⟨c.1 t, hav t⟩) (fun u => ⟨ρ u, hρ1 u⟩) with hs'
  have hp := congrFun hprof s'
  have hr : ∀ (S : Fin (n + b) → Fin (20 * n) × Fin M) (hh : List (StatisticalQuery _)),
      replayQueries (encode m) S hh =
        replayQueries (m (fun t => decide ((S (Fin.natAdd n t)).1.val % 2 = 0)))
          (fun t => S (Fin.castAdd b t)) hh := fun _ _ => rfl
  have hσ : (fun u => decide ((rowSample r (fun t => (s' t).val) (Fin.natAdd n u)).1.val % 2 = 0))
      = c.2 := by
    funext u
    simp [hs', rowSample, Fin.append_right, hρ2]
  have hS : (fun t => rowSample r (fun t => (s' t).val) (Fin.castAdd b t)) =
      fun t => supportEmbedding r (c.1 t) := by
    funext t
    simp [hs', rowSample, Fin.append_left]
    rfl
  simp only [responseProfile] at hp
  rw [hr] at hp
  simp only [encode] at hp
  rw [hσ, hS] at hp
  exact hp

theorem attackS (hn : 0 < n) (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (T : Tr n M) (hT : (survS m r T).Nonempty)
    (p : ThresholdPath (20 * n)) (hp : p.common = commonS (survS m r T))
    (Θ : Fin (p.length + 1) → Table (20 * n) M)
    (hΘ : ∀ ℓ (x : Fin (20 * n) × Fin M), x.2 = r x.1 → Θ ℓ x = thresholdPattern p ℓ x.1)
    (hag : profilesAgree (encode m) r (T.map Prod.fst) p Θ) :
    ∃ ℓ, SepS hN m r T (Θ ℓ) := by
  classical
  set e := supportEmbedding r with he
  set H := survS m r T with hH
  have hhpos : (0 : ℝ) < H.card := by exact_mod_cast hT.card_pos
  by_contra hns
  have hns' : ∀ ℓ, ∃ a : ℝ, |a - populationMean (uniformSupport hN e) (liftQuery (Θ ℓ))| ≤ 1 / 10 ∧
      (9 / 10 : ℝ) * H.card <
        (((H.filter (fun c => mechS m r c T (Θ ℓ) = a)).card : ℕ) : ℝ) := by
    intro ℓ
    by_contra hq
    apply hns
    refine ⟨ℓ, fun a ha => ?_⟩
    push Not at hq
    exact hq a ha
  choose a ha hbig using hns'
  have hmean : ∀ ℓ, populationMean (uniformSupport hN e) (liftQuery (Θ ℓ)) =
      ((Finset.univ.filter (fun i => thresholdPattern p ℓ i = true)).card : ℝ) /
        ((20 * n : ℕ) : ℝ) := by
    intro ℓ
    rw [IsRandomnessNecessaryADA.Plain.Dev.L12.mean_gen hN e (Θ ℓ),
      ← IsRandomnessNecessaryADA.Plain.Dev.L12.bitSum_pattern]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show bitValue (Θ ℓ (i, r i)) = _
    rw [hΘ ℓ (i, r i) rfl]
  set C := commonS H with hC
  have hCcard : (C.card : ℝ) ≤ 5 / 4 * n := by
    have := commonS_card H
    have h2 : (8 / 10 : ℝ) * (C.card : ℝ) ≤ n := by
      by_contra hcon
      push Not at hcon
      nlinarith
    linarith
  have hNr : (0 : ℝ) < ((20 * n : ℕ) : ℝ) := by exact_mod_cast hN
  have hlt : ∀ ℓ : Fin (p.length + 1), ℓ = 0 → a ℓ < 1 / 2 := by
    intro ℓ hℓ
    subst hℓ
    have hsub : Finset.univ.filter (fun i => thresholdPattern p 0 i = true) ⊆ C := by
      intro i hi
      have hi' := (Finset.mem_filter.1 hi).2
      simp only [thresholdPattern, decide_eq_true_eq] at hi'
      rw [← hp]
      rcases hi' with h1 | ⟨t, ht, _⟩
      · exact h1
      · simp at ht
    have hc : ((Finset.univ.filter (fun i => thresholdPattern p 0 i = true)).card : ℝ) ≤ C.card := by
      exact_mod_cast Finset.card_le_card hsub
    have h1 := ha 0
    rw [hmean 0] at h1
    have hmean' : ((Finset.univ.filter (fun i => thresholdPattern p 0 i = true)).card : ℝ) /
        ((20 * n : ℕ) : ℝ) ≤ 1 / 16 := by
      rw [div_le_iff₀ hNr]; push_cast; nlinarith
    have := (abs_le.1 h1).2
    linarith
  have hge : ¬ a (Fin.last p.length) < 1 / 2 := by
    have hall : Finset.univ.filter (fun i => thresholdPattern p (Fin.last p.length) i = true) =
        Finset.univ := by
      refine Finset.filter_true_of_mem (fun i _ => ?_)
      simp only [thresholdPattern, decide_eq_true_eq]
      by_cases hi : i ∈ p.common
      · exact Or.inl hi
      · right
        have := (p.complement i).not.1 hi
        push Not at this
        obtain ⟨t, ht⟩ := this
        exact ⟨t, by simp, ht⟩
    have h1 := ha (Fin.last p.length)
    rw [hmean, hall] at h1
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    rw [div_self hNr.ne'] at h1
    have := (abs_le.1 h1).1
    intro hlt'
    linarith
  obtain ⟨t, ht1, ht2⟩ : ∃ t : Fin p.length, a t.castSucc < 1 / 2 ∧ ¬ a t.succ < 1 / 2 := by
    by_contra hcon
    push Not at hcon
    have : ∀ ℓ : Fin (p.length + 1), a ℓ < 1 / 2 := by
      intro ℓ
      induction ℓ using Fin.induction with
      | zero => exact hlt 0 rfl
      | succ i ih => exact lt_of_not_ge (fun hh => absurd hh (not_le.2 (hcon i ih)))
    exact hge (this _)
  set i := p.change t with hi
  have hiC : i ∉ C := by
    intro hmem
    rw [← hp] at hmem
    exact (p.complement i).1 hmem t rfl
  set W1 := H.filter (fun c => mechS m r c T (Θ t.castSucc) = a t.castSucc) with hW1
  set W2 := H.filter (fun c => mechS m r c T (Θ t.succ) = a t.succ) with hW2
  have hW1H : W1 ⊆ H := fun s hs => (Finset.mem_filter.1 hs).1
  have hW2H : W2 ⊆ H := fun s hs => (Finset.mem_filter.1 hs).1
  have hsub : W1 ∩ W2 ⊆ H.filter (fun c => ∃ t', c.1 t' = i) := by
    intro c hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_inter.1 hs
    refine Finset.mem_filter.2 ⟨hW1H hs1, ?_⟩
    by_contra hcon
    push Not at hcon
    have h1 : mechS m r c T (Θ t.castSucc) = a t.castSucc := (Finset.mem_filter.1 hs1).2
    have h2 : mechS m r c T (Θ t.succ) = a t.succ := (Finset.mem_filter.1 hs2).2
    have hcons : consS m r c T := by
      have := hW1H hs1
      simpa [hH, survS] using this
    have hrep : replayQueries (m c.2) (fun t => supportEmbedding r (c.1 t))
        ((T.map Prod.fst).map liftQuery) = lt T := by
      have hTh : (lt T).map Prod.fst = (T.map Prod.fst).map liftQuery := by
        simp [lt, List.map_map, Function.comp_def]
      rw [← hTh]; exact hcons
    have hb := bit_agree hn m r (T.map Prod.fst) i _ _ (hag t) c hcon
    rw [hrep] at hb
    change responseBit (mechS m r c T (Θ t.castSucc)) = responseBit (mechS m r c T (Θ t.succ))
      at hb
    rw [h1, h2] at hb
    have e1 : responseBit (a t.castSucc) = false := by
      simp only [responseBit, decide_eq_false_iff_not, not_le]; exact ht1
    have e2 : responseBit (a t.succ) = true := by
      simp only [responseBit, decide_eq_true_eq]; exact not_lt.1 ht2
    rw [e1, e2] at hb
    exact Bool.false_ne_true hb
  have hcard1 : ((W1 ∩ W2).card : ℝ) ≤ ((H.filter (fun c => ∃ t', c.1 t' = i)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hnc : ((H.filter (fun c => ∃ t', c.1 t' = i)).card : ℝ) < (8 / 10 : ℝ) * H.card := by
    by_contra hcon
    push Not at hcon
    apply hiC
    rw [hC]
    unfold commonS
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    convert hcon
  have hu : ((W1 ∪ W2).card : ℝ) ≤ H.card := by
    exact_mod_cast Finset.card_le_card (Finset.union_subset hW1H hW2H)
  have hi2 : ((W1 ∪ W2).card : ℝ) + (W1 ∩ W2).card = W1.card + W2.card := by
    exact_mod_cast Finset.card_union_add_card_inter W1 W2
  have := hbig t.castSucc
  have := hbig t.succ
  linarith

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
  IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {n M b : ℕ}
variable (Kc : ∀ (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (p : ThresholdPath (20 * n)),
  PMF (Fin (p.length + 1) → Table (20 * n) M))
theorem fwS_fst (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (c : Cand n b) (j : ℕ) :
    (fwS Kc hN m r c j).map Prod.fst = randRun (mechS m r) (qlawS Kc hN m r) c [] j := by
  induction j with
  | zero => simp [fwS, randRun, PMF.pure_map]
  | succ j ih =>
    rw [IsRandomnessNecessaryADA.Plain.Dev.L12.randRun_last, ← ih, fwS, PMF.map_bind, PMF.bind_map]
    congr 1
    funext x
    simp only [stepS, qlawS, PMF.map_comp, Function.comp_def]

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {n M b : ℕ}
variable (Kc : ∀ (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (p : ThresholdPath (20 * n)),
  PMF (Fin (p.length + 1) → Table (20 * n) M))
alias fwS_fst := IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP.fwS_fst

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
  IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {n M b : ℕ}
variable (Kc : ∀ (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (p : ThresholdPath (20 * n)),
  PMF (Fin (p.length + 1) → Table (20 * n) M))
theorem qlawS_le (hKm : ∀ r h p j, (Kc r h p).map (fun Q => Q j) =
      completionLaw r (thresholdPattern p j))
    (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (T : Tr n M) (q : Table (20 * n) M) :
    ((qlawS Kc hN m r T) q).toReal ≤
      (densityFactor (20 * n) : ℝ) / Fintype.card (Table (20 * n) M) := by
  classical
  set p := pathS m r T with hp
  set K := Kc r (T.map Prod.fst) p with hK
  have hL : p.length ≤ 20 * n := by
    simpa using Fintype.card_le_of_embedding p.change
  set joint : PMF ((Fin (p.length + 1) → Table (20 * n) M) × Fin (p.length + 1)) :=
    K.map (fun Θ => (Θ, selS hN m r T p Θ)) with hjoint
  have hmarg : ∀ j, joint.map (fun w => w.1 j) = completionLaw r (thresholdPattern p j) := by
    intro j
    rw [hjoint, PMF.map_comp]
    exact hKm _ _ _ j
  have h42 := lemma_4_2 (20 * n) M p.length hL r (fun j => thresholdPattern p j) joint hmarg {q}
  have e1 : joint.map (fun w => w.1 w.2) = qlawS Kc hN m r T := by
    rw [hjoint, PMF.map_comp]; rfl
  rw [e1] at h42
  unfold probability at h42
  rw [PMF.toOuterMeasure_apply_singleton] at h42
  have e2 : ((tableLaw (20 * n) M).toOuterMeasure {q}).toReal =
      1 / Fintype.card (Table (20 * n) M) := by
    unfold tableLaw
    rw [PMF.toOuterMeasure_apply_singleton]
    simp [PMF.uniformOfFintype_apply]
  rw [e2] at h42
  calc _ ≤ _ := h42
    _ = _ := by ring

theorem margS_density (hKm : ∀ r h p j, (Kc r h p).map (fun Q => Q j) =
      completionLaw r (thresholdPattern p j))
    (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (c : Cand n b) (j : ℕ) :
    ∀ T, (((fwS Kc hN m r c j).map Prod.fst) T) ≤
      ENNReal.ofReal ((densityFactor (20 * n) : ℝ) / Fintype.card (Table (20 * n) M)) ^ j := by
  classical
  set cc := ENNReal.ofReal ((densityFactor (20 * n) : ℝ) / Fintype.card (Table (20 * n) M)) with hc
  have hq : ∀ T q, (qlawS Kc hN m r T) q ≤ cc := by
    intro T q
    rw [hc, ENNReal.le_ofReal_iff_toReal_le (PMF.apply_ne_top _ _) (by positivity)]
    exact qlawS_le Kc hKm hN m r T q
  induction j with
  | zero =>
    intro T
    simp only [fwS, PMF.pure_map, pow_zero]
    exact PMF.coe_le_one _ _
  | succ j ih =>
    intro T'
    rw [fwS_fst, IsRandomnessNecessaryADA.Plain.Dev.L12.randRun_last, ← fwS_fst, PMF.bind_apply,
      pow_succ]
    by_cases hT' : T' = []
    · subst hT'
      have : ∀ T, ((qlawS Kc hN m r T).map (fun q => T ++ [(q, mechS m r c T q)])) [] = 0 := by
        intro T
        rw [PMF.apply_eq_zero_iff, PMF.support_map]
        rintro ⟨q, _, hq0⟩
        simp at hq0
      simp [this]
    · rw [tsum_eq_single T'.dropLast]
      · refine mul_le_mul' (ih _) (IsRandomnessNecessaryADA.Plain.Dev.L12.map_apply_le _ _ ?_ cc
          (hq _) _)
        intro q q' hqq
        have := List.append_cancel_left hqq
        exact (Prod.mk.inj (List.cons.inj this).1).1
      · intro T hT
        have : ((qlawS Kc hN m r T).map (fun q => T ++ [(q, mechS m r c T q)])) T' = 0 := by
          rw [PMF.apply_eq_zero_iff, PMF.support_map]
          rintro ⟨q, _, hq0⟩
          apply hT
          rw [← hq0]
          simp
        rw [this, mul_zero]

theorem fwS_support (hKm : ∀ r h p j, (Kc r h p).map (fun Q => Q j) =
      completionLaw r (thresholdPattern p j))
    (hN : 0 < 20 * n) (hn : 0 < n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (c : Cand n b) (j : ℕ) :
    ∀ x ∈ (fwS Kc hN m r c j).support, x.1.length = j ∧ consS m r c x.1 ∧
      (x.2 = false → (∀ qa ∈ lt x.1,
          |qa.2 - populationMean (uniformSupport hN (supportEmbedding r)) qa.1| ≤ 1 / 10) →
        ((survS m r x.1).card : ℝ) ≤
          (9 / 10 : ℝ) ^ j * ((2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n)) := by
  classical
  induction j with
  | zero =>
    intro x hx
    simp only [fwS, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨rfl, consS_nil m r c, fun _ _ => ?_⟩
    have : (survS m r ([] : Tr n M)).card ≤ Fintype.card (Cand n b) := Finset.card_le_univ _
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at this
    have h' : ((survS m r ([] : Tr n M)).card : ℝ) ≤ ((20 * n : ℕ) : ℝ) ^ n * (2 : ℝ) ^ b := by
      exact_mod_cast this
    simp only [pow_zero, one_mul]
    linarith
  | succ j ih =>
    intro x' hx'
    simp only [fwS, PMF.mem_support_bind_iff] at hx'
    obtain ⟨x, hx, hx'⟩ := hx'
    obtain ⟨T, f⟩ := x
    obtain ⟨hlen, hcons, hinv⟩ := ih (T, f) hx
    simp only [stepS, PMF.mem_support_map_iff] at hx'
    obtain ⟨Θ, hΘ, rfl⟩ := hx'
    simp only at hlen hcons hinv hΘ ⊢
    set q := Θ (selS hN m r T (pathS m r T) Θ) with hq
    refine ⟨by simp [hlen], (consS_snoc m r c T q _).2 ⟨hcons, rfl⟩, ?_⟩
    intro hflag hacc
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not] at hflag
    obtain ⟨hf, hag⟩ := hflag
    have hacc' : ∀ qa ∈ lt T,
        |qa.2 - populationMean (uniformSupport hN (supportEmbedding r)) qa.1| ≤ 1 / 10 := by
      intro qa hqa
      refine hacc qa ?_
      simp only [lt, List.map_append, List.mem_append]
      exact Or.inl (by simpa [lt] using hqa)
    have hcardT := hinv hf hacc'
    have hne : (survS m r T).Nonempty := ⟨c, by simpa [survS] using hcons⟩
    have hΘsupp : ∀ ℓ (y : Fin (20 * n) × Fin M), y.2 = r y.1 →
        Θ ℓ y = thresholdPattern (pathS m r T) ℓ y.1 := by
      intro ℓ y hy
      refine IsRandomnessNecessaryADA.Plain.Dev.L12.supp_pattern
        ((Kc r (T.map Prod.fst) (pathS m r T)).map (fun Q => Q ℓ)) r _ (hKm _ _ _ _) (Θ ℓ) ?_ y hy
      exact (PMF.mem_support_map_iff _ _ _).2 ⟨Θ, hΘ, rfl⟩
    have hex := attackS hn hN m r T hne (pathS m r T) rfl Θ hΘsupp hag
    have hsel : SepS hN m r T q := by
      simp only [hq, selS, dif_pos hex]
      exact Classical.choose_spec hex
    have hnew := hacc (liftQuery q, mechS m r c T q) (by simp [lt])
    have hfilt := hsel (mechS m r c T q) hnew
    have hsub : survS m r (T ++ [(q, mechS m r c T q)]) ⊆
        (survS m r T).filter (fun c' => mechS m r c' T q = mechS m r c T q) := by
      intro c' hc'
      have : consS m r c' (T ++ [(q, mechS m r c T q)]) := by simpa [survS] using hc'
      obtain ⟨h1, h2⟩ := (consS_snoc m r c' T q _).1 this
      exact Finset.mem_filter.2 ⟨by simpa [survS] using h1, h2⟩
    have hc2 : ((survS m r (T ++ [(q, mechS m r c T q)])).card : ℝ) ≤ (9 / 10 : ℝ) *
        (survS m r T).card :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) hfilt
    calc ((survS m r (T ++ [(q, mechS m r c T q)])).card : ℝ)
        ≤ (9 / 10 : ℝ) * (survS m r T).card := hc2
      _ ≤ (9 / 10 : ℝ) * ((9 / 10 : ℝ) ^ j * ((2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n)) := by
        gcongr
      _ = _ := by ring

theorem fwS_error (hKm : ∀ r h p j, (Kc r h p).map (fun Q => Q j) =
      completionLaw r (thresholdPattern p j))
    (hN : 0 < 20 * n) (hn : 0 < n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (c : Cand n b) :
    ∀ x ∈ (fwS Kc hN m r c (horizonS n b)).support, x.2 = false →
      lt x.1 ∈ errorEvent (uniformSupport hN (supportEmbedding r)) (1 / 10) := by
  classical
  intro x hx hf
  by_contra herr
  obtain ⟨_, hcons, hinv⟩ := fwS_support Kc hKm hN hn m r c _ x hx
  have hacc : ∀ qa ∈ lt x.1,
      |qa.2 - populationMean (uniformSupport hN (supportEmbedding r)) qa.1| ≤ 1 / 10 := by
    intro qa hqa
    by_contra hq
    exact herr ⟨qa, hqa, not_le.1 hq⟩
  have hcard := hinv hf hacc
  have hpos : (1 : ℝ) ≤ (survS m r x.1).card := by
    exact_mod_cast Finset.card_pos.2 ⟨c, by simpa [survS] using hcons⟩
  have hh := horizonS_pos n b hn
  set k := horizonS n b
  have h9 : (9 / 10 : ℝ) ^ k * (10 / 9 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
  have h10 : (9 / 10 : ℝ) ^ k * ((2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n) < 1 := by
    calc (9 / 10 : ℝ) ^ k * ((2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n)
        < (9 / 10 : ℝ) ^ k * (10 / 9 : ℝ) ^ k := by gcongr
      _ = 1 := h9
  linarith

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {n M b : ℕ}
variable (Kc : ∀ (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (p : ThresholdPath (20 * n)),
  PMF (Fin (p.length + 1) → Table (20 * n) M))
alias fwS_error := IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP.fwS_error

alias margS_density := IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartP.margS_density

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartS
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
  IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun derand)
theorem tom_le_one {α : Type} (p : PMF α) (s : Set α) : p.toOuterMeasure s ≤ 1 := by
  rw [← (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)]
  exact MeasureTheory.measure_mono (Set.subset_univ s)

theorem exists_ofFn {α : Type} (j : ℕ) (l : List α) (hl : l.length = j) :
    ∃ h : Fin j → α, List.ofFn h = l := by
  subst hl
  exact ⟨l.get, List.ofFn_get l⟩

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartS
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartS
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
  IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun derand)
variable {n M b : ℕ}
/-- the transcript obtained by answering the tables of `L` in order with sample `s` -/
noncomputable def replayT (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (r : Locations (20 * n) M)
    (c : Cand n b) (L : List (Table (20 * n) M)) : Tr n M :=
  L.foldl (fun T q => T ++ [(q, mechS m r c T q)]) []

theorem foldl_map_fst (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (r : Locations (20 * n) M)
    (c : Cand n b) (L : List (Table (20 * n) M)) : ∀ T0 : Tr n M,
    (L.foldl (fun T q => T ++ [(q, mechS m r c T q)]) T0).map Prod.fst = T0.map Prod.fst ++ L := by
  induction L with
  | nil => intro T0; simp
  | cons q L ih => intro T0; simp [List.foldl_cons, ih]

theorem replayT_map_fst (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (r : Locations (20 * n) M)
    (c : Cand n b) (L : List (Table (20 * n) M)) :
    (replayT m r c L).map Prod.fst = L := by
  simpa [replayT] using foldl_map_fst m r c L []

theorem replayT_snoc (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (r : Locations (20 * n) M)
    (c : Cand n b) (L : List (Table (20 * n) M)) (q : Table (20 * n) M) :
    replayT m r c (L ++ [q]) = replayT m r c L ++ [(q, mechS m r c (replayT m r c L) q)] := by
  simp [replayT, List.foldl_append]

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartS
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartS
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
  IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun derand)
variable {n M b : ℕ}
variable (Kc : ∀ (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (p : ThresholdPath (20 * n)),
  PMF (Fin (p.length + 1) → Table (20 * n) M))
theorem fw_replay (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (c : Cand n b) (j : ℕ) :
    ∀ x ∈ (fwS Kc hN m r c j).support,
      x.1 = replayT m r c (x.1.map Prod.fst) ∧ x.1.length = j := by
  induction j with
  | zero =>
    intro x hx
    simp only [fwS, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    simp [replayT]
  | succ j ih =>
    intro x' hx'
    simp only [fwS, PMF.mem_support_bind_iff] at hx'
    obtain ⟨x, hx, hx'⟩ := hx'
    obtain ⟨h1, h2⟩ := ih x hx
    simp only [stepS, PMF.mem_support_map_iff] at hx'
    obtain ⟨Θ, _, rfl⟩ := hx'
    refine ⟨?_, by simp [h2]⟩
    simp only [List.map_append, List.map_cons, List.map_nil, replayT_snoc]
    rw [← h1]

/-- the flag probability after `j` rounds -/
noncomputable def U (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (c : Cand n b) (j : ℕ) : ENNReal :=
  (fwS Kc hN m r c j).toOuterMeasure {x | x.2 = true}

/-- the one-round coupling failure probability at transcript `T` -/
noncomputable def Bm (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (T : Tr n M) : ENNReal :=
  (Kc r (T.map Prod.fst) (pathS m r T)).toOuterMeasure
    {Θ | ¬ profilesAgree (encode m) r (T.map Prod.fst) (pathS m r T) Θ}

theorem Bm_le_one (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (T : Tr n M) : Bm Kc m r T ≤ 1 := tom_le_one _ _

theorem U_succ (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (c : Cand n b) (j : ℕ) :
    U Kc hN m r c (j + 1) ≤
      U Kc hN m r c j + ∑' T, ((fwS Kc hN m r c j).map Prod.fst) T * Bm Kc m r T := by
  have hx : ∀ x : Tr n M × Bool, (stepS Kc hN m r c x).toOuterMeasure {y | y.2 = true} ≤
      (if x.2 = true then 1 else 0) + Bm Kc m r x.1 := by
    intro x
    obtain ⟨T, b⟩ := x
    cases b
    · simp only [stepS, PMF.toOuterMeasure_map_apply, Bm]
      refine le_trans (le_of_eq ?_) le_add_self
      congr 1
      ext Θ
      simp
    · exact (tom_le_one _ _).trans (by simp)
  have hmap : ∑' T, ((fwS Kc hN m r c j).map Prod.fst) T * Bm Kc m r T =
      ∑' x, fwS Kc hN m r c j x * Bm Kc m r x.1 := by
    simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    congr 1
    funext x
    simp_rw [ite_mul, zero_mul]
    exact tsum_ite_eq x.1 (fun T => fwS Kc hN m r c j x * Bm Kc m r T)
  rw [U, fwS, PMF.toOuterMeasure_bind_apply, hmap, U, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum (fun x => ?_)
  calc fwS Kc hN m r c j x * (stepS Kc hN m r c x).toOuterMeasure {y | y.2 = true}
      ≤ fwS Kc hN m r c j x * ((if x.2 = true then 1 else 0) + Bm Kc m r x.1) :=
        mul_le_mul_right (hx x) _
    _ = _ := by
        rw [mul_add]
        congr 1
        by_cases h : x.2 = true <;> simp [Set.indicator, h]

theorem dens_sum (hKm : ∀ r h p j, (Kc r h p).map (fun Q => Q j) =
      completionLaw r (thresholdPattern p j))
    (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (c : Cand n b) (j : ℕ) :
    ∑' T, ((fwS Kc hN m r c j).map Prod.fst) T * Bm Kc m r T ≤
      ENNReal.ofReal ((densityFactor (20 * n) : ℝ) / Fintype.card (Table (20 * n) M)) ^ j *
        ∑ h : Fin j → Table (20 * n) M, Bm Kc m r (replayT m r c (List.ofFn h)) := by
  have hinj : Function.Injective
      (fun h : Fin j → Table (20 * n) M => replayT m r c (List.ofFn h)) := by
    intro h1 h2 e
    have := congrArg (List.map Prod.fst) e
    simp only [replayT_map_fst] at this
    exact List.ofFn_injective this
  have hsupp : Function.support (fun T => ((fwS Kc hN m r c j).map Prod.fst) T * Bm Kc m r T) ⊆
      Set.range (fun h : Fin j → Table (20 * n) M => replayT m r c (List.ofFn h)) := by
    intro T hT
    have h1 : ((fwS Kc hN m r c j).map Prod.fst) T ≠ 0 := left_ne_zero_of_mul hT
    rw [← PMF.mem_support_iff, PMF.support_map] at h1
    obtain ⟨x, hx, rfl⟩ := h1
    obtain ⟨hrep, hlen⟩ := fw_replay Kc hN m r c j x hx
    obtain ⟨h, hh⟩ := exists_ofFn j (x.1.map Prod.fst) (by simp [hlen])
    exact ⟨h, by simp only; rw [hh, ← hrep]⟩
  rw [← hinj.tsum_eq hsupp, tsum_fintype, Finset.mul_sum]
  exact Finset.sum_le_sum (fun h _ => mul_le_mul_left (margS_density Kc hKm hN m r c j _) _)

theorem sum_r_bound (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (β : ℝ) (hβ : 0 ≤ β)
    (hbound : ∀ (h : List (Table (20 * n) M)) (path : Locations (20 * n) M → ThresholdPath (20 * n)),
        ∑ r, ((Kc r h (path r)).toOuterMeasure
            {Q | ¬ profilesAgree (encode m) r h (path r) Q}).toReal ≤ β)
    (c : Cand n b) (L : List (Table (20 * n) M)) :
    ∑ r, Bm Kc m r (replayT m r c L) ≤ ENNReal.ofReal β := by
  have hfin : ∀ r, Bm Kc m r (replayT m r c L) ≠ ⊤ :=
    fun r => ne_top_of_le_ne_top ENNReal.one_ne_top (Bm_le_one _ _ _ _)
  rw [ENNReal.le_ofReal_iff_toReal_le (ENNReal.sum_ne_top.2 (fun r _ => hfin r)) hβ,
    ENNReal.toReal_sum (fun r _ => hfin r)]
  have := hbound L (fun r => pathS m r (replayT m r c L))
  simpa only [Bm, replayT_map_fst] using this

theorem dens_card :
    ENNReal.ofReal ((densityFactor (20 * n) : ℝ) / Fintype.card (Table (20 * n) M)) *
      (Fintype.card (Table (20 * n) M) : ENNReal) = (densityFactor (20 * n) : ENNReal) := by
  have hc : (Fintype.card (Table (20 * n) M) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← ENNReal.ofReal_natCast (Fintype.card _), ← ENNReal.ofReal_mul (by positivity),
    div_mul_cancel₀ _ hc, ENNReal.ofReal_natCast]

theorem sumU (hKm : ∀ r h p j, (Kc r h p).map (fun Q => Q j) =
      completionLaw r (thresholdPattern p j))
    (hN : 0 < 20 * n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b) (β : ℝ) (hβ : 0 ≤ β)
    (hbound : ∀ (h : List (Table (20 * n) M)) (path : Locations (20 * n) M → ThresholdPath (20 * n)),
        ∑ r, ((Kc r h (path r)).toOuterMeasure
            {Q | ¬ profilesAgree (encode m) r h (path r) Q}).toReal ≤ β)
    (c : Cand n b) (j : ℕ) :
    ∑ r, U Kc hN m r c j ≤
      (j : ENNReal) * (densityFactor (20 * n) : ENNReal) ^ j * ENNReal.ofReal β := by
  induction j with
  | zero => simp [U, fwS, PMF.toOuterMeasure_pure_apply]
  | succ j ih =>
    set cc := ENNReal.ofReal ((densityFactor (20 * n) : ℝ) / Fintype.card (Table (20 * n) M))
    set D : ENNReal := (densityFactor (20 * n) : ENNReal) with hD
    set β' := ENNReal.ofReal β
    have hc : cc ^ j * (Fintype.card (Fin j → Table (20 * n) M) : ENNReal) = D ^ j := by
      rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ← mul_pow, dens_card]
    have hD1 : 1 ≤ D := by
      rw [hD]
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by simp [densityFactor])
    calc ∑ r, U Kc hN m r c (j + 1)
        ≤ ∑ r, (U Kc hN m r c j + ∑' T, ((fwS Kc hN m r c j).map Prod.fst) T * Bm Kc m r T) :=
          Finset.sum_le_sum (fun r _ => U_succ Kc hN m r c j)
      _ = ∑ r, U Kc hN m r c j + ∑ r, ∑' T, ((fwS Kc hN m r c j).map Prod.fst) T * Bm Kc m r T :=
          Finset.sum_add_distrib
      _ ≤ j * D ^ j * β' + ∑ r, cc ^ j *
            ∑ h : Fin j → Table (20 * n) M, Bm Kc m r (replayT m r c (List.ofFn h)) :=
          add_le_add ih (Finset.sum_le_sum (fun r _ => dens_sum Kc hKm hN m r c j))
      _ = j * D ^ j * β' + cc ^ j *
            ∑ h : Fin j → Table (20 * n) M, ∑ r, Bm Kc m r (replayT m r c (List.ofFn h)) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ j * D ^ j * β' + cc ^ j * ∑ _h : Fin j → Table (20 * n) M, β' := by
          gcongr with h
          exact sum_r_bound Kc m β hβ hbound c _
      _ = j * D ^ j * β' + D ^ j * β' := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hc]
      _ ≤ j * D ^ (j + 1) * β' + D ^ (j + 1) * β' := by
          have := pow_le_pow_right₀ hD1 (Nat.le_succ j)
          gcongr
      _ = ((j + 1 : ℕ) : ENNReal) * D ^ (j + 1) * β' := by push_cast; ring

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartS
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartS
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
  IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun derand)
theorem const_bound (n M b : ℕ) (hn : 0 < n) (hM : columnCountS n b ≤ M) :
    ((horizonS n b : ℕ) : ℝ) * ((densityFactor (20 * n) : ℕ) : ℝ) ^ horizonS n b *
      epsG (20 * n) (n + b) M ≤ 1 / 200 := by
  set k := horizonS n b with hk
  set D := densityFactor (20 * n) with hD
  set N := 20 * n with hNdef
  have hN1 : 1 ≤ N := by omega
  have hk1 : 1 ≤ k := by simp [hk, horizonS]
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (by simp [hD, densityFactor])
  have hM' : ((2 * N ^ (n + b) * (100 * k * N * 2 ^ N * D ^ k) ^ 2 : ℕ) : ℝ) ≤ M := by
    exact_mod_cast hM
  push_cast at hM'
  set X : ℝ := 100 * k * N * 2 ^ N * D ^ k with hX
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hXpos : 0 < X := by positivity
  have hNn : 0 < (N : ℝ) ^ (n + b) := by positivity
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hM'
  have hsq : Real.sqrt (2 * (N : ℝ) ^ (n + b) / M) ≤ 1 / X := by
    rw [Real.sqrt_le_left (by positivity), div_le_iff₀ hMpos]
    calc 2 * (N : ℝ) ^ (n + b) = (1 / X) ^ 2 * (2 * N ^ (n + b) * X ^ 2) := by field_simp
      _ ≤ (1 / X) ^ 2 * M := by gcongr
  have h2 : (2 : ℝ) ^ N = 2 * 2 ^ (N - 1) := by
    rw [← pow_succ']; congr 1; omega
  have heps : epsG N (n + b) M ≤ (N : ℝ) * 2 ^ (N - 1) * (1 / X) := by
    unfold epsG
    gcongr
  calc (k : ℝ) * (D : ℝ) ^ k * epsG N (n + b) M ≤
        (k : ℝ) * (D : ℝ) ^ k * ((N : ℝ) * 2 ^ (N - 1) * (1 / X)) := by
        gcongr
    _ = 1 / 200 := by
        rw [hX, h2]
        field_simp
        ring

theorem one_le_bad_add_U {n M b : ℕ}
    (Kc : ∀ (r : Locations (20 * n) M) (h : List (Table (20 * n) M)) (p : ThresholdPath (20 * n)),
      PMF (Fin (p.length + 1) → Table (20 * n) M))
    (hKm : ∀ r h p j, (Kc r h p).map (fun Q => Q j) = completionLaw r (thresholdPattern p j))
    (hN : 0 < 20 * n) (hn : 0 < n) (m : SeedMechanism (Fin (20 * n) × Fin M) n b)
    (r : Locations (20 * n) M) (c : Cand n b) :
    1 ≤ ((randRun (mechS m r) (qlawS Kc hN m r) c [] (horizonS n b)).toOuterMeasure
          {T | lt T ∈ errorEvent (uniformSupport hN (supportEmbedding r)) (1 / 10)}).toReal +
        (U Kc hN m r c (horizonS n b)).toReal := by
  set F := fwS Kc hN m r c (horizonS n b)
  set A : Set (Tr n M × Bool) :=
    Prod.fst ⁻¹' {T | lt T ∈ errorEvent (uniformSupport hN (supportEmbedding r)) (1 / 10)}
  set B : Set (Tr n M × Bool) := {x | x.2 = true}
  have h1 : F.toOuterMeasure (A ∪ B) = 1 := by
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro x hx
    by_cases hb : x.2 = true
    · exact Or.inr hb
    · exact Or.inl (fwS_error Kc hKm hN hn m r c x hx (by simpa using hb))
  have h2 : 1 ≤ F.toOuterMeasure A + F.toOuterMeasure B :=
    h1 ▸ MeasureTheory.measure_union_le A B
  rw [← fwS_fst Kc hN m r c, PMF.toOuterMeasure_map_apply]
  have hA : F.toOuterMeasure A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (tom_le_one _ _)
  have hB : F.toOuterMeasure B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (tom_le_one _ _)
  show (1 : ℝ) ≤ (F.toOuterMeasure A).toReal + (F.toOuterMeasure B).toReal
  rw [← ENNReal.toReal_add hA hB]
  calc (1 : ℝ) = (1 : ENNReal).toReal := by simp
    _ ≤ _ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hA, hB⟩) h2

theorem card_cand (n b : ℕ) :
    ((Fintype.card (Cand n b) : ℕ) : ℝ) = ((20 * n : ℕ) : ℝ) ^ n * (2 : ℝ) ^ b := by
  simp [Cand, PrivateSeed, Fintype.card_prod, Fintype.card_bool]

open scoped Classical in
theorem main_seed (n : ℕ) (hn : 0 < n) (b M : ℕ) [NeZero M] (hM : columnCountS n b ≤ M)
    (m : SeedMechanism (Fin (20 * n) × Fin M) n b) :
    ∃ (r : Locations (20 * n) M) (A : Tr n M → Table (20 * n) M),
      (99 / 100 : ℝ) ≤ (1 / (((20 * n : ℕ) : ℝ) ^ n * (2 : ℝ) ^ b)) *
        ∑ c : Cand n b,
          (if lt (detRun (mechS m r) A c [] (horizonS n b)) ∈
              errorEvent (uniformSupport (by omega : 0 < 20 * n) (supportEmbedding r)) (1 / 10)
            then (1 : ℝ) else 0) := by
  have hN : 0 < 20 * n := by omega
  set k := horizonS n b with hk
  set D := densityFactor (20 * n) with hD
  have hk1 : 1 ≤ k := by simp [hk, horizonS]
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (by simp [hD, densityFactor])
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  set δ : ℝ := 1 / (200 * k * (D : ℝ) ^ k) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨Kc, hKm, hbound⟩ := near_opt_gen (20 * n) M (n + b) hN (encode m) δ hδ
  set L : ℝ := (Fintype.card (Locations (20 * n) M) : ℝ) with hL
  set β : ℝ := L * (epsG (20 * n) (n + b) M + δ) with hβdef
  have heps : 0 ≤ epsG (20 * n) (n + b) M := by unfold epsG; positivity
  have hβ : 0 ≤ β := by positivity
  have hkey : ∀ c, ∑ r, (U Kc hN m r c k).toReal ≤ L / 100 := by
    intro c
    have h1 := sumU Kc hKm hN m β hβ hbound c k
    have he : (k : ENNReal) * (D : ENNReal) ^ k * ENNReal.ofReal β =
        ENNReal.ofReal ((k : ℝ) * (D : ℝ) ^ k * β) := by
      rw [ENNReal.ofReal_mul (p := (k : ℝ) * (D : ℝ) ^ k) (by positivity),
        ENNReal.ofReal_mul (p := (k : ℝ)) (by positivity),
        ENNReal.ofReal_pow (p := (D : ℝ)) (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
    have hfin : ∀ r, U Kc hN m r c k ≠ ⊤ :=
      fun r => ne_top_of_le_ne_top ENNReal.one_ne_top (tom_le_one _ _)
    rw [he, ENNReal.le_ofReal_iff_toReal_le (ENNReal.sum_ne_top.2 (fun r _ => hfin r))
      (by positivity), ENNReal.toReal_sum (fun r _ => hfin r)] at h1
    refine h1.trans ?_
    have hc := const_bound n M b hn hM
    have hd : (k : ℝ) * (D : ℝ) ^ k * δ = 1 / 200 := by
      rw [hδdef]; field_simp
    have hL0 : 0 ≤ L := by positivity
    calc (k : ℝ) * (D : ℝ) ^ k * β =
          L * ((k : ℝ) * (D : ℝ) ^ k * epsG (20 * n) (n + b) M + k * (D : ℝ) ^ k * δ) := by
          rw [hβdef]; ring
      _ ≤ L * (1 / 200 + 1 / 200) := by rw [hd]; gcongr
      _ = L / 100 := by ring
  set P : Locations (20 * n) M → Cand n b → ℝ := fun r c =>
    ((randRun (mechS m r) (qlawS Kc hN m r) c [] k).toOuterMeasure
      {T | lt T ∈ errorEvent (uniformSupport hN (supportEmbedding r)) (1 / 10)}).toReal with hP
  have hPU : ∀ r c, 1 ≤ P r c + (U Kc hN m r c k).toReal :=
    fun r c => one_le_bad_add_U Kc hKm hN hn m r c
  set Nn : ℝ := ((20 * n : ℕ) : ℝ) ^ n * (2 : ℝ) ^ b with hNn
  have hNnpos : 0 < Nn := by positivity
  have hcardS : ((Fintype.card (Cand n b) : ℕ) : ℝ) = Nn := card_cand n b
  have hsum : ∑ _r : Locations (20 * n) M, Nn * (99 / 100) ≤ ∑ r, ∑ c, P r c := by
    calc ∑ _r : Locations (20 * n) M, Nn * (99 / 100)
        = ∑ _c : Cand n b, (L - L / 100) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardS, hL]; ring
      _ ≤ ∑ c : Cand n b, (L - ∑ r, (U Kc hN m r c k).toReal) := by
          gcongr with c; exact hkey c
      _ = ∑ c : Cand n b, ∑ r, (1 - (U Kc hN m r c k).toReal) := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.sum_sub_distrib]; simp [hL]
      _ ≤ ∑ c : Cand n b, ∑ r, P r c := by
          gcongr with c _ r; linarith [hPU r c]
      _ = ∑ r, ∑ c, P r c := Finset.sum_comm
  obtain ⟨r, -, hr⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  obtain ⟨A, hA⟩ := derand (mechS m r) (consS m r) (consS_snoc m r)
    (fun _ => 1 / Nn) (fun _ => by positivity)
    (fun T => lt T ∈ errorEvent (uniformSupport hN (supportEmbedding r)) (1 / 10)) k
    (qlawS Kc hN m r) []
  refine ⟨r, A, ?_⟩
  simp only [consS_nil, if_true, true_and] at hA
  rw [Finset.mul_sum]
  refine le_trans ?_ hA
  rw [← Finset.mul_sum]
  calc (99 / 100 : ℝ) = 1 / Nn * (Nn * (99 / 100)) := by field_simp
    _ ≤ 1 / Nn * ∑ c, P r c := by gcongr

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartS
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
alias main_seed := IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartS.main_seed

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartQ
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {α β : Type}
/-! ### The i.i.d. law -/
theorem iid_succ' (μ : PMF α) (n : ℕ) :
    iid μ (n + 1) = μ.bind fun a => (iid μ n).map (Fin.cons a) := rfl

theorem iid_map' (μ : PMF α) (g : α → β) :
    ∀ n, iid (μ.map g) n = (iid μ n).map fun s j => g (s j)
  | 0 => by
    show PMF.pure Fin.elim0 = (PMF.pure Fin.elim0).map _
    rw [PMF.pure_map]
    congr 1
    funext j
    exact j.elim0
  | n + 1 => by
    rw [iid_succ', iid_succ', iid_map' μ g n, PMF.bind_map, PMF.map_bind]
    congr 1
    funext a
    simp only [Function.comp_apply, PMF.map_comp]
    congr 1
    funext t j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp

open scoped Classical in
theorem map_cons_apply' {n : ℕ} (ν : PMF (Fin n → α)) (a : α) (s : Fin (n + 1) → α) :
    (ν.map (Fin.cons a)) s = if s 0 = a then ν (Fin.tail s) else 0 := by
  rw [PMF.map_apply]
  split_ifs with h
  · rw [tsum_eq_single (Fin.tail s)]
    · rw [if_pos]
      rw [← h, Fin.cons_self_tail]
    · intro t ht
      rw [if_neg]
      rintro rfl
      exact ht (by simp)
  · refine ENNReal.tsum_eq_zero.2 fun t => if_neg ?_
    rintro rfl
    exact h (Fin.cons_zero _ _)

theorem iid_apply' (μ : PMF α) : ∀ (n : ℕ) (s : Fin n → α), iid μ n s = ∏ j, μ (s j)
  | 0, s => by
    show (PMF.pure Fin.elim0) s = _
    simp only [PMF.pure_apply, Finset.univ_eq_empty, Finset.prod_empty]
    rw [if_pos]
    funext j
    exact j.elim0
  | n + 1, s => by
    rw [iid_succ', PMF.bind_apply, Fin.prod_univ_succ]
    simp_rw [map_cons_apply']
    rw [tsum_eq_single (s 0)]
    · rw [if_pos rfl, iid_apply' μ n]
      rfl
    · intro b hb
      rw [if_neg (Ne.symm hb), mul_zero]

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartQ
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartQ
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
open scoped Classical in
theorem prob_unif {N n : ℕ} (hN : 0 < N) {Ω : Type} (h : (Fin n → Fin N) → Ω) (E : Set Ω) :
    probability ((iid (uniformFin N hN) n).map h) E =
      (1 / (N : ℝ) ^ n) * ∑ s : Fin n → Fin N, (if h s ∈ E then (1 : ℝ) else 0) := by
  unfold probability
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have hval : (iid (uniformFin N hN) n s).toReal = 1 / (N : ℝ) ^ n := by
      rw [iid_apply']
      simp [uniformFin, PMF.uniformOfFintype_apply]
    by_cases hs : h s ∈ E
    · have : s ∈ h ⁻¹' E := hs
      rw [Set.indicator_of_mem this, hval, if_pos hs, mul_one]
    · have : s ∉ h ⁻¹' E := hs
      rw [Set.indicator_of_notMem this, if_neg hs]
      simp
  · intro s _
    by_cases hs : s ∈ h ⁻¹' E
    · rw [Set.indicator_of_mem hs]; exact PMF.apply_ne_top _ _
    · rw [Set.indicator_of_notMem hs]; exact ENNReal.zero_ne_top

/-! ### Population means -/
theorem mean_formula {N : ℕ} (hN : 0 < N) {X : Type} [Fintype X] (e : Fin N ↪ X)
    (q : StatisticalQuery X) :
    populationMean (uniformSupport hN e) q = (∑ i, (q (e i)).val) / N := by
  classical
  unfold populationMean uniformSupport
  have hp : ∀ i, ((uniformFin N hN) i).toReal = 1 / (N : ℝ) := by
    intro i
    unfold uniformFin
    simp [PMF.uniformOfFintype_apply]
  have hmap : ∀ x : X, ((PMF.map e (uniformFin N hN)) x).toReal =
      ∑ i : Fin N, if x = e i then 1 / (N : ℝ) else 0 := by
    intro x
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : x = e i
      · simp [h, hp]
      · simp [h]
    · intro i _
      split_ifs
      · exact PMF.apply_ne_top _ _
      · simp
  simp only [hmap, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, ∑ x : X, (if x = e i then 1 / (N : ℝ) else 0) *
      (q x).val = 1 / (N : ℝ) * (q (e i)).val := by
    intro i
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp
  simp only [this]
  rw [← Finset.mul_sum]
  ring

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartQ
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartQ
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
variable {Y Z : Type} (φ : Y ≃ Z)
/-! ### Transport along an equivalence -/
def trQ (q : StatisticalQuery Y) : StatisticalQuery Z := fun z => q (φ.symm z)

def trT (T : Transcript (StatisticalQuery Y)) : Transcript (StatisticalQuery Z) :=
  T.map (fun qa => (trQ φ qa.1, qa.2))

def m0 {n : ℕ} (m : Mechanism Z n) : Mechanism Y n :=
  fun S T q => m (fun t => φ (S t)) (trT φ T) (trQ φ q)

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartQ
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartQ
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
noncomputable def decT {n M : ℕ} {Z : Type} (φ : Fin (20 * n) × Fin M ≃ Z)
    (T : Transcript (StatisticalQuery Z)) : Tr n M :=
  T.map (fun qa => (fun x => decide ((1 / 2 : ℝ) ≤ (qa.1 (φ x)).val), qa.2))

theorem decT_trT_lt {n M : ℕ} {Z : Type} (φ : Fin (20 * n) × Fin M ≃ Z) (T : Tr n M) :
    decT φ (trT φ (lt T)) = T := by
  unfold decT trT lt
  rw [List.map_map, List.map_map]
  conv_rhs => rw [← List.map_id T]
  refine List.map_congr_left (fun qa _ => ?_)
  obtain ⟨q, a⟩ := qa
  show (_, a) = (q, a)
  congr 1
  funext x
  simp only [trQ, Equiv.symm_apply_apply, liftQuery]
  cases q x <;> norm_num [bitValue]

theorem detRun_last {S Q : Type} [Fintype S] [Fintype Q] [Nonempty Q]
    (mech : S → List (Q × ℝ) → Q → ℝ) (A : List (Q × ℝ) → Q) (s : S) (j : ℕ) :
    ∀ T0, detRun mech A s T0 (j + 1) =
      detRun mech A s T0 j ++ [(A (detRun mech A s T0 j),
        mech s (detRun mech A s T0 j) (A (detRun mech A s T0 j)))] := by
  induction j with
  | zero => intro T0; rfl
  | succ j ih => intro T0; exact ih _

def m0S {Y Z : Type} {n b : ℕ} (φ : Y ≃ Z) (m : SeedMechanism Z n b) : SeedMechanism Y n b :=
  fun σ => m0 φ (m σ)

theorem run_eq {n M b : ℕ} [NeZero M] {Z : Type} (φ : Fin (20 * n) × Fin M ≃ Z)
    (m : SeedMechanism Z n b) (r : Locations (20 * n) M) (A : Tr n M → Table (20 * n) M)
    (s : Fin n → Fin (20 * n)) (σ : PrivateSeed b) (j : ℕ) :
    interaction (m σ) (liftAnalyst (fun T z => A (decT φ T) (φ.symm z)))
        (fun t => φ (supportEmbedding r (s t))) j =
      trT φ (lt (detRun (mechS (m0S φ m) r) A (s, σ) [] j)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [interaction, detRun_last]
    rw [ih]
    set D := detRun (mechS (m0S φ m) r) A (s, σ) [] j
    have hq : liftAnalyst (fun T z => A (decT φ T) (φ.symm z)) (trT φ (lt D)) =
        trQ φ (liftQuery (A D)) := by
      show liftQuery (fun z => A (decT φ (trT φ (lt D))) (φ.symm z)) = _
      rw [decT_trT_lt]
      rfl
    rw [hq]
    simp only [trT, lt, List.map_append, List.map_cons, List.map_nil]
    rfl

theorem err_tr {n M : ℕ} {Z : Type} [Fintype Z] (φ : Fin (20 * n) × Fin M ≃ Z)
    (r : Locations (20 * n) M) (hN : 0 < 20 * n)
    (T : Transcript (StatisticalQuery (Fin (20 * n) × Fin M))) (ε : ℝ)
    (h : T ∈ errorEvent (uniformSupport hN (supportEmbedding r)) ε) :
    trT φ T ∈ errorEvent (uniformSupport hN ((supportEmbedding r).trans φ.toEmbedding)) ε := by
  obtain ⟨qa, hmem, hlt⟩ := h
  refine ⟨(trQ φ qa.1, qa.2), List.mem_map.2 ⟨qa, hmem, rfl⟩, ?_⟩
  rw [mean_formula] at hlt ⊢
  simpa [trQ] using hlt

/-! ### The seed law -/
theorem prob_seed {b : ℕ} {Ω : Type} (f : PrivateSeed b → PMF Ω) (E : Set Ω) :
    probability ((seedLaw b).bind f) E = ∑ σ, (1 / (2 : ℝ) ^ b) * probability (f σ) E := by
  unfold probability
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [ENNReal.toReal_mul]
    congr 1
    simp [seedLaw, PMF.uniformOfFintype_apply]
  · intro σ _
    refine ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ?_
    rw [PMF.toOuterMeasure_apply]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      ((ENNReal.tsum_le_tsum fun x => Set.indicator_le_self E (f σ) x).trans_eq (f σ).tsum_coe)

/-! ### Arithmetic -/
theorem horizonS_pos (n b : ℕ) : 0 < horizonS n b := by
  unfold horizonS; omega

theorem columnCountS_pos (n b : ℕ) (hn : 0 < n) : 0 < columnCountS n b := by
  have hk := horizonS_pos n b
  apply Nat.pos_of_ne_zero
  simp [columnCountS, densityFactor, hk.ne', hn.ne']

theorem twenty_le (n : ℕ) : 20 * n ≤ 2 ^ (5 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ (5 * n) := Nat.one_le_two_pow
    rw [show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    omega

theorem twenty_succ_le (n : ℕ) (hn : 0 < n) : 20 * n + 1 ≤ 2 ^ (5 * n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; norm_num
    · have := ih h0
      rw [show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
      omega

theorem d_le_pow (n b : ℕ) (hn : 0 < n) :
    20 * n * columnCountS n b ≤ 2 ^ (15 + 55 * n + 5 * n * (n + b) + 2 * horizonS n b +
      50 * n * horizonS n b) := by
  set k := horizonS n b with hkdef
  have h1 := twenty_le n
  have h2 := twenty_succ_le n hn
  have hD : densityFactor (20 * n) ≤ 2 ^ (25 * n) := by
    unfold densityFactor
    calc (20 * n + 1) * 2 ^ (20 * n) ≤ 2 ^ (5 * n) * 2 ^ (20 * n) := Nat.mul_le_mul h2 le_rfl
      _ = 2 ^ (25 * n) := by rw [← pow_add]; ring_nf
  have hDk : densityFactor (20 * n) ^ k ≤ 2 ^ (25 * n * k) :=
    (Nat.pow_le_pow_left hD k).trans_eq (by rw [← pow_mul])
  have hkk : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
  have hNn : (20 * n) ^ (n + b) ≤ 2 ^ (5 * n * (n + b)) :=
    (Nat.pow_le_pow_left h1 (n + b)).trans_eq (by rw [← pow_mul])
  have inner : 100 * k * (20 * n) * 2 ^ (20 * n) * densityFactor (20 * n) ^ k ≤
      2 ^ (7 + k + 5 * n + 20 * n + 25 * n * k) := by
    calc 100 * k * (20 * n) * 2 ^ (20 * n) * densityFactor (20 * n) ^ k ≤
        2 ^ 7 * 2 ^ k * 2 ^ (5 * n) * 2 ^ (20 * n) * 2 ^ (25 * n * k) := by
          gcongr; norm_num
      _ = _ := by simp only [← pow_add]
  show 20 * n * (2 * (20 * n) ^ (n + b) * (100 * k * (20 * n) * 2 ^ (20 * n) *
      densityFactor (20 * n) ^ k) ^ 2) ≤ _
  calc 20 * n * (2 * (20 * n) ^ (n + b) * (100 * k * (20 * n) * 2 ^ (20 * n) *
      densityFactor (20 * n) ^ k) ^ 2) ≤
      2 ^ (5 * n) * (2 ^ 1 * 2 ^ (5 * n * (n + b)) *
        (2 ^ (7 + k + 5 * n + 20 * n + 25 * n * k)) ^ 2) := by
        gcongr; norm_num
    _ = _ := by
        rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
        congr 1
        ring

theorem log_twenty_le (n : ℕ) (hn : 2 < n) : Real.log ((20 * n : ℕ) : ℝ) ≤ 4 * Real.log n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h20 : (20 : ℝ) * n ≤ (n : ℝ) ^ 4 := by
    have h3 : (3 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hnR 3
    have : (n : ℝ) ^ 4 = n * n ^ 3 := by ring
    rw [this]; nlinarith
  push_cast
  calc Real.log (20 * n) ≤ Real.log ((n : ℝ) ^ 4) := Real.log_le_log (by positivity) h20
    _ = 4 * Real.log n := by rw [Real.log_pow]; norm_num

theorem log_ten_ninths : (1 / 10 : ℝ) ≤ Real.log (10 / 9) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 / 10 by norm_num)
  have : Real.log (9 / 10 : ℝ) = - Real.log (10 / 9) := by
    rw [← Real.log_inv]; norm_num
  linarith

theorem horizonS_le (n b : ℕ) (hn : 2 < n) :
    (horizonS n b : ℝ) ≤ 42 * ((n : ℝ) * (Real.log n / Real.log 2) + b) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hL : 1 ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hlog2, one_mul]
    exact Real.log_le_log (by norm_num) (by linarith)
  set L := Real.log n / Real.log 2 with hLdef
  have hlogn : Real.log n = L * Real.log 2 := by
    rw [hLdef]; field_simp
  have hN0 : (0 : ℝ) < ((20 * n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 20 * n by omega)
  have hnum : Real.log ((2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n) =
      b * Real.log 2 + n * Real.log ((20 * n : ℕ) : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hlogN := log_twenty_le n hn
  have hlogN0 : 0 ≤ Real.log ((20 * n : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 20 * n by omega))
  set num := Real.log ((2 : ℝ) ^ b * ((20 * n : ℕ) : ℝ) ^ n) with hnumdef
  have hnum0 : 0 ≤ num := by
    rw [hnum]; positivity
  have hx0 : 0 ≤ num / Real.log (10 / 9) :=
    div_nonneg hnum0 (by linarith [log_ten_ninths])
  have hx : num / Real.log (10 / 9) ≤ 10 * num := by
    calc num / Real.log (10 / 9) ≤ num / (1 / 10) :=
          div_le_div_of_nonneg_left hnum0 (by norm_num) log_ten_ninths
      _ = 10 * num := by ring
  have hceil := Nat.ceil_lt_add_one hx0
  have hk : (horizonS n b : ℝ) ≤ 10 * num + 2 := by
    show (((⌈num / Real.log (10 / 9)⌉₊ + 1 : ℕ)) : ℝ) ≤ _
    push_cast
    linarith
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have e1 : num ≤ b + 4 * n * L := by
    rw [hnum]
    have a1 : (b : ℝ) * Real.log 2 ≤ b := by nlinarith
    have a2 : (n : ℝ) * Real.log ((20 * n : ℕ) : ℝ) ≤ n * (4 * Real.log n) :=
      mul_le_mul_of_nonneg_left hlogN hnn
    have a3 : (n : ℝ) * (4 * Real.log n) ≤ 4 * n * L := by
      rw [hlogn]
      have : (0 : ℝ) ≤ 4 * n * L := by positivity
      nlinarith
    linarith
  have e2 : (3 : ℝ) ≤ n * L := by nlinarith
  linarith

/-! ### The theorem -/
theorem chk_theorem_1_4 :
    ∃ C_X C_k : ℝ, 0 < C_X ∧ 0 < C_k ∧
      ∀ (n : ℕ) (hn : 2 < n) (b : ℕ), ∃ d k : ℕ,
        0 < d ∧ 0 < k ∧
        (d : ℝ) ≤ (2 : ℝ) ^
          (C_X * ((n : ℝ) ^ 2 * (Real.log n / Real.log 2) + (n : ℝ) * b)) ∧
        (k : ℝ) ≤ C_k * ((n : ℝ) * (Real.log n / Real.log 2) + b) ∧
        ∀ m : SeedMechanism (Fin d) n b,
          ∃ (e : Fin (20 * n) ↪ Fin d) (A : BooleanAnalyst (Fin d)),
            (9 / 10 : ℝ) ≤
              probability (seedInteractionLaw m (liftAnalyst A)
                (uniformSupport (by omega) e) k)
                (errorEvent (uniformSupport (by omega) e) (1 / 10)) := by
  refine ⟨2300, 42, by norm_num, by norm_num, ?_⟩
  intro n hn b
  have hn0 : 0 < n := by omega
  have hMpos : 0 < columnCountS n b := columnCountS_pos n b hn0
  have : NeZero (columnCountS n b) := ⟨hMpos.ne'⟩
  set k := horizonS n b with hkdef
  have hk' : (k : ℝ) ≤ 42 * ((n : ℝ) * (Real.log n / Real.log 2) + b) := horizonS_le n b hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 1 ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hlog2, one_mul]
    exact Real.log_le_log (by norm_num) (by linarith)
  refine ⟨20 * n * columnCountS n b, k, Nat.mul_pos (by omega) hMpos, horizonS_pos n b, ?_, hk', ?_⟩
  · set L := Real.log n / Real.log 2 with hLdef
    have hE : ((15 + 55 * n + 5 * n * (n + b) + 2 * k + 50 * n * k : ℕ) : ℝ) ≤
        2300 * ((n : ℝ) ^ 2 * L + n * b) := by
      push_cast
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
      have a1 : (15 : ℝ) + 55 * n + 5 * n ^ 2 ≤ 75 * n ^ 2 * L := by
        have : (15 : ℝ) + 55 * n + 5 * n ^ 2 ≤ 75 * n ^ 2 := by nlinarith
        have h2 : (0 : ℝ) ≤ 75 * n ^ 2 := by positivity
        nlinarith
      have a2 : (2 : ℝ) * k + 50 * n * k ≤ 52 * n * k := by nlinarith
      have a3 : (52 : ℝ) * n * k ≤ 52 * n * (42 * (n * L + b)) := by
        have : (0 : ℝ) ≤ 52 * n := by positivity
        exact mul_le_mul_of_nonneg_left hk' this
      have a4 : (0 : ℝ) ≤ n * b := by positivity
      have a5 : (0 : ℝ) ≤ n ^ 2 * L := by positivity
      nlinarith
    calc ((20 * n * columnCountS n b : ℕ) : ℝ)
        ≤ ((2 ^ (15 + 55 * n + 5 * n * (n + b) + 2 * k + 50 * n * k) : ℕ) : ℝ) := by
          exact_mod_cast d_le_pow n b hn0
      _ = (2 : ℝ) ^ (((15 + 55 * n + 5 * n * (n + b) + 2 * k + 50 * n * k : ℕ)) : ℝ) := by
          rw [Real.rpow_natCast]; push_cast; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
  · intro m
    classical
    let φ : Fin (20 * n) × Fin (columnCountS n b) ≃ Fin (20 * n * columnCountS n b) :=
      finProdFinEquiv
    obtain ⟨r, A, hA⟩ := main_seed n hn0 b (columnCountS n b) le_rfl (m0S φ m)
    refine ⟨(supportEmbedding r).trans φ.toEmbedding, fun T z => A (decT φ T) (φ.symm z), ?_⟩
    set E := errorEvent (uniformSupport (by omega : 0 < 20 * n)
      ((supportEmbedding r).trans φ.toEmbedding)) (1 / 10) with hEdef
    set I : Cand n b → ℝ := fun c =>
      if lt (detRun (mechS (m0S φ m) r) A c [] k) ∈
          errorEvent (uniformSupport (by omega : 0 < 20 * n) (supportEmbedding r)) (1 / 10)
        then (1 : ℝ) else 0 with hIdef
    have hper : ∀ σ : PrivateSeed b,
        (1 / ((20 * n : ℕ) : ℝ) ^ n) * ∑ s : Fin n → Fin (20 * n), I (s, σ) ≤
          probability (interactionLaw (m σ) (liftAnalyst (fun T z => A (decT φ T) (φ.symm z)))
            (uniformSupport (by omega) ((supportEmbedding r).trans φ.toEmbedding)) k) E := by
      intro σ
      unfold interactionLaw uniformSupport
      rw [iid_map', PMF.map_comp, prob_unif]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => ?_)) (by positivity)
      simp only [hIdef]
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exfalso; apply h2
        have := err_tr φ r (by omega) _ _ h1
        rw [← run_eq φ m r A s σ k] at this
        exact this
      · norm_num
      · exact le_rfl
    have hsum : (1 / (((20 * n : ℕ) : ℝ) ^ n * (2 : ℝ) ^ b)) * ∑ c : Cand n b, I c =
        ∑ σ : PrivateSeed b, (1 / (2 : ℝ) ^ b) *
          ((1 / ((20 * n : ℕ) : ℝ) ^ n) * ∑ s : Fin n → Fin (20 * n), I (s, σ)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      ring
    unfold seedInteractionLaw
    rw [prob_seed]
    refine le_trans (by norm_num) (hA.trans ?_)
    rw [hsum]
    exact Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hper σ) (by positivity))

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartQ
end

section
set_option autoImplicit false
namespace IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
open IsRandomnessNecessaryADA.Plain IsRandomnessNecessaryADA.Plain.Supplement
open IsRandomnessNecessaryADA.Plain.Dev.L12 (Tr lt mkPath detRun randRun)
alias chk_theorem_1_4 := IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.PartQ.chk_theorem_1_4

end IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14
end

open IsRandomnessNecessaryADA.Plain.Supplement in
theorem solution : type_of% @IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.chk_theorem_1_4 := @IsRandomnessNecessaryADA.Plain.Supplement.Dev.L14.chk_theorem_1_4
