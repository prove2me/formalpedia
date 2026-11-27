-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.switching_lemma_dnf
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:21:55.112854+00:00
-- url     : https://prove2.me/submissions/b5b81359-c082-4d51-b8b1-a29532477693

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting
import Definitions.Def_HypercliqueAC0_FixedDepth_Switching

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

variable {X : Type}

/-- set the coordinates in `S` to the values of `g` -/
def SWL_setTo (ρ : X → Option Bool) (S : Finset X) (g : X → Bool) : X → Option Bool :=
  fun e => if e ∈ S then some (g e) else ρ e

def SWL_cons (T : Finset (X × Bool)) : Prop := ∀ e, ¬ ((e, true) ∈ T ∧ (e, false) ∈ T)
def SWL_sig (T : Finset (X × Bool)) : X → Bool := fun e => decide ((e, true) ∈ T)
def SWL_vars (T : Finset (X × Bool)) : Finset X := T.image Prod.fst
def SWL_fals (T : Finset (X × Bool)) (ρ : X → Option Bool) : Prop := ∃ l ∈ T, ρ l.1 = some (!l.2)
def SWL_sat (T : Finset (X × Bool)) (ρ : X → Option Bool) : Prop := ∀ l ∈ T, ρ l.1 = some l.2
def SWL_stars (T : Finset (X × Bool)) (ρ : X → Option Bool) : Finset X :=
  (SWL_vars T).filter (fun e => ρ e = none)

/-- canonical decision tree depth -/
def SWL_cd : List (Finset (X × Bool)) → (X → Option Bool) → ℕ
  | [], _ => 0
  | T :: L, ρ =>
    if ¬ SWL_cons T then SWL_cd L ρ
    else if SWL_fals T ρ then SWL_cd L ρ
    else if SWL_stars T ρ = ∅ then 0
    else (SWL_stars T ρ).card + (SWL_stars T ρ).powerset.sup
      (fun P => SWL_cd L (SWL_setTo ρ (SWL_stars T ρ) (fun e => decide (e ∈ P))))

def SWL_dnf (L : List (Finset (X × Bool))) (x : X → Bool) : Bool :=
  decide (∃ T ∈ L, termValue T x = true)

lemma SWL_sig_eq {T : Finset (X × Bool)} (hc : SWL_cons T) {l : X × Bool} (hl : l ∈ T) :
    SWL_sig T l.1 = l.2 := by
  obtain ⟨e, b⟩ := l
  cases b
  · simp only [SWL_sig, decide_eq_false_iff_not]
    intro h; exact hc e ⟨h, hl⟩
  · simpa [SWL_sig] using hl

lemma SWL_dt_mono {t : ℕ} {f : (X → Bool) → Bool} (h : DTDepthLE t f) :
    ∀ {t'}, t ≤ t' → DTDepthLE t' f := by
  induction h with
  | const t b => intro t' _; exact DTDepthLE.const t' b
  | query t i f h0 h1 ih0 ih1 =>
    intro t' ht'
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    exact DTDepthLE.query t'' i f (ih0 (by omega)) (ih1 (by omega))

lemma SWL_dt_const {t : ℕ} {f : (X → Bool) → Bool} (b : Bool) (h : ∀ x, f x = b) :
    DTDepthLE t f := by
  have : f = fun _ => b := funext h
  rw [this]; exact DTDepthLE.const t b

lemma SWL_dt_query (f : (X → Bool) → Bool) (d : ℕ) (S : Finset X) :
    ∀ (ρ : X → Option Bool), (∀ e ∈ S, ρ e = none) →
      (∀ g : X → Bool, DTDepthLE d (restrictFn (SWL_setTo ρ S g) f)) →
      DTDepthLE (S.card + d) (restrictFn ρ f) := by
  induction S using Finset.induction_on with
  | empty =>
    intro ρ _ h
    have := h (fun _ => true)
    have e : SWL_setTo ρ ∅ (fun _ => true) = ρ := by funext e; simp [SWL_setTo]
    rw [e] at this; simpa using this
  | insert i S hi ih =>
    intro ρ hρ h
    have hc : (insert i S).card + d = (S.card + d) + 1 := by
      rw [Finset.card_insert_of_notMem hi]; omega
    rw [hc]
    have key : ∀ b : Bool, DTDepthLE (S.card + d)
        (fun x => restrictFn ρ f (Function.update x i b)) := by
      intro b
      have e1 : (fun x => restrictFn ρ f (Function.update x i b)) =
          restrictFn (Function.update ρ i (some b)) f := by
        funext x
        simp only [restrictFn]
        congr 1
        funext e
        by_cases he : e = i
        · subst he; simp [hρ e (Finset.mem_insert_self _ _)]
        · simp [he]
      rw [e1]
      apply ih
      · intro e he
        have hne : e ≠ i := fun h => hi (h ▸ he)
        simp [hne, hρ e (Finset.mem_insert_of_mem he)]
      · intro g
        have e2 : SWL_setTo (Function.update ρ i (some b)) S g =
            SWL_setTo ρ (insert i S) (Function.update g i b) := by
          funext e
          by_cases he : e = i
          · subst he; simp [SWL_setTo, hi]
          · by_cases hS : e ∈ S <;> simp [SWL_setTo, he, hS]
        rw [e2]; exact h _
    exact DTDepthLE.query _ i _ (key false) (key true)

lemma SWL_fals_restrict {T : Finset (X × Bool)} {L : List (Finset (X × Bool))}
    {ρ : X → Option Bool} (h : SWL_fals T ρ) :
    restrictFn ρ (SWL_dnf (T :: L)) = restrictFn ρ (SWL_dnf L) := by
  funext x
  obtain ⟨l, hl, hρ⟩ := h
  have : termValue T (fun e => (ρ e).getD (x e)) = false := by
    simp only [termValue, decide_eq_false_iff_not, not_forall]
    exact ⟨l, hl, by simp [hρ]⟩
  simp [restrictFn, SWL_dnf, this]

lemma SWL_dt_cd (L : List (Finset (X × Bool))) :
    ∀ ρ, DTDepthLE (SWL_cd L ρ) (restrictFn ρ (SWL_dnf L)) := by
  induction L with
  | nil =>
    intro ρ
    exact SWL_dt_const false (fun x => by simp [restrictFn, SWL_dnf])
  | cons T L ih =>
    intro ρ
    by_cases hc : SWL_cons T
    swap
    · have e : restrictFn ρ (SWL_dnf (T :: L)) = restrictFn ρ (SWL_dnf L) := by
        funext x
        have : termValue T (fun e => (ρ e).getD (x e)) = false := by
          simp only [termValue, decide_eq_false_iff_not]
          intro hall
          simp only [SWL_cons, not_forall, not_not] at hc
          obtain ⟨e, h1, h2⟩ := hc
          have a1 := hall _ h1
          have a2 := hall _ h2
          simp at a1 a2; rw [a1] at a2; exact Bool.noConfusion a2
        simp [restrictFn, SWL_dnf, this]
      simp only [SWL_cd, hc, not_false_eq_true, if_true]
      rw [e]; exact ih ρ
    by_cases hf : SWL_fals T ρ
    · simp only [SWL_cd, hc, hf, not_true_eq_false, if_false, if_true]
      rw [SWL_fals_restrict hf]; exact ih ρ
    -- not falsified: every literal var is a star or fixed correctly
    have hfix : ∀ l ∈ T, ρ l.1 ≠ none → ρ l.1 = some l.2 := by
      intro l hl hn
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hn
      rw [hb]
      by_cases hbl : b = l.2
      · rw [hbl]
      · exfalso; apply hf; refine ⟨l, hl, ?_⟩; rw [hb]; congr 1
        cases b <;> cases h2 : l.2 <;> simp_all
    by_cases hS : SWL_stars T ρ = ∅
    · simp only [SWL_cd, hc, hf, hS, not_true_eq_false, if_false, if_true]
      apply SWL_dt_const true
      intro x
      have : termValue T (fun e => (ρ e).getD (x e)) = true := by
        simp only [termValue, decide_eq_true_eq]
        intro l hl
        have hn : ρ l.1 ≠ none := by
          intro hn
          have : l.1 ∈ SWL_stars T ρ := by
            simp only [SWL_stars, SWL_vars, Finset.mem_filter, Finset.mem_image]
            exact ⟨⟨l, hl, rfl⟩, hn⟩
          rw [hS] at this; simp at this
        simp [hfix l hl hn]
      simp only [restrictFn, SWL_dnf, decide_eq_true_eq]
      exact ⟨T, List.mem_cons_self, this⟩
    simp only [SWL_cd, hc, hf, hS, not_true_eq_false, if_false]
    set S := SWL_stars T ρ with hSdef
    apply SWL_dt_query _ _ S ρ
    · intro e he
      simp only [hSdef, SWL_stars, Finset.mem_filter] at he
      exact he.2
    intro g
    by_cases hg : ∀ e ∈ S, g e = SWL_sig T e
    · apply SWL_dt_const true
      intro x
      have : termValue T (fun e => (SWL_setTo ρ S g e).getD (x e)) = true := by
        simp only [termValue, decide_eq_true_eq]
        intro l hl
        by_cases hlS : l.1 ∈ S
        · simp [SWL_setTo, hlS, hg _ hlS, SWL_sig_eq hc hl]
        · have hn : ρ l.1 ≠ none := by
            intro hn; apply hlS
            simp only [hSdef, SWL_stars, SWL_vars, Finset.mem_filter, Finset.mem_image]
            exact ⟨⟨l, hl, rfl⟩, hn⟩
          simp [SWL_setTo, hlS, hfix l hl hn]
      simp only [restrictFn, SWL_dnf, decide_eq_true_eq]
      exact ⟨T, List.mem_cons_self, this⟩
    · push Not at hg
      obtain ⟨e, heS, hge⟩ := hg
      have hfg : SWL_fals T (SWL_setTo ρ S g) := by
        have : e ∈ SWL_vars T := by
          simp only [hSdef, SWL_stars, Finset.mem_filter] at heS; exact heS.1
        simp only [SWL_vars, Finset.mem_image] at this
        obtain ⟨l, hl, rfl⟩ := this
        refine ⟨l, hl, ?_⟩
        have := SWL_sig_eq hc hl
        simp only [SWL_setTo, heS, if_true]
        congr 1
        rw [this] at hge
        cases h1 : g l.1 <;> cases h2 : l.2 <;> simp_all
      rw [SWL_fals_restrict hfg]
      apply SWL_dt_mono (ih _)
      have e3 : SWL_setTo ρ S g = SWL_setTo ρ S (fun e => decide (e ∈ S.filter (fun e => g e = true))) := by
        funext e
        by_cases he : e ∈ S <;> simp [SWL_setTo, he]
      rw [e3]
      exact Finset.le_sup (f := fun P => SWL_cd L (SWL_setTo ρ S (fun e => decide (e ∈ P))))
        (Finset.mem_powerset.mpr (Finset.filter_subset _ _))

def SWL_up (U : (X → Option Bool) → Prop) : Prop :=
  ∀ ρ ρ', U ρ → (∀ e, ρ e ≠ none → ρ' e = ρ e) → U ρ'

lemma SWL_up_and {U V : (X → Option Bool) → Prop} (hU : SWL_up U) (hV : SWL_up V) :
    SWL_up (fun ρ => U ρ ∧ V ρ) :=
  fun ρ ρ' h hr => ⟨hU ρ ρ' h.1 hr, hV ρ ρ' h.2 hr⟩

lemma SWL_up_fals (T : Finset (X × Bool)) : SWL_up (SWL_fals T) := by
  intro ρ ρ' ⟨l, hl, h⟩ hr
  exact ⟨l, hl, by rw [hr _ (by simp [h]), h]⟩

lemma SWL_up_sat (T : Finset (X × Bool)) : SWL_up (SWL_sat T) := by
  intro ρ ρ' h hr l hl
  rw [hr _ (by simp [h l hl]), h l hl]

section counting
variable [Fintype X]

lemma SWL_sw_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (o : Option Bool) : 0 ≤ starWeight p o := by
  cases o <;> simp [starWeight] <;> linarith

lemma SWL_wt_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (ρ : X → Option Bool) :
    0 ≤ restrictionWeight p ρ :=
  Finset.prod_nonneg (fun _ _ => SWL_sw_nonneg hp hp1 _)

lemma SWL_prob_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (E : (X → Option Bool) → Prop) :
    0 ≤ restrictionProb p E :=
  Finset.sum_nonneg (fun ρ _ => by split_ifs; exact SWL_wt_nonneg hp hp1 ρ; exact le_rfl)

lemma SWL_prob_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) {E E' : (X → Option Bool) → Prop}
    (h : ∀ ρ, E ρ → E' ρ) : restrictionProb p E ≤ restrictionProb p E' := by
  unfold restrictionProb
  apply Finset.sum_le_sum
  intro ρ _
  by_cases h1 : E ρ
  · simp [h1, h ρ h1]
  · simp only [h1, if_false]; split_ifs; exact SWL_wt_nonneg hp hp1 ρ; exact le_rfl

lemma SWL_prob_congr {p : ℝ} {E E' : (X → Option Bool) → Prop}
    (h : ∀ ρ, E ρ ↔ E' ρ) : restrictionProb p E = restrictionProb p E' := by
  unfold restrictionProb
  apply Finset.sum_congr rfl
  intro ρ _
  simp only [h ρ]

lemma SWL_prob_split (p : ℝ) (E Q : (X → Option Bool) → Prop) :
    restrictionProb p E = restrictionProb p (fun ρ => E ρ ∧ Q ρ) +
      restrictionProb p (fun ρ => E ρ ∧ ¬ Q ρ) := by
  unfold restrictionProb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases h1 : E ρ <;> by_cases h2 : Q ρ <;> simp [h1, h2]

lemma SWL_prob_disj (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (E A B : (X → Option Bool) → Prop)
    (h : ∀ ρ, A ρ → B ρ → False) :
    restrictionProb p (fun ρ => E ρ ∧ A ρ) + restrictionProb p (fun ρ => E ρ ∧ B ρ) ≤
      restrictionProb p E := by
  unfold restrictionProb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ρ _
  have := SWL_wt_nonneg hp hp1 ρ
  by_cases h1 : E ρ <;> by_cases h2 : A ρ <;> by_cases h3 : B ρ <;> simp [h1, h2, h3, this]
  exact (h ρ h2 h3).elim

lemma SWL_inj_sum (P Q : (X → Option Bool) → Prop) {hP : DecidablePred P} {hQ : DecidablePred Q} (f : (X → Option Bool) → (X → Option Bool))
    (g : (X → Option Bool) → ℝ) (hg : ∀ a, 0 ≤ g a)
    (hinj : ∀ a b, P a → P b → f a = f b → a = b) (hmap : ∀ a, P a → Q (f a)) :
    (∑ a, if P a then g (f a) else 0) ≤ ∑ a, if Q a then g a else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  rw [← Finset.sum_image (g := f) (f := g)]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro b hb
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      obtain ⟨a, ha, rfl⟩ := hb
      exact hmap a ha
    · intro i _ _; exact hg i
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
    exact hinj a b ha hb hab

lemma SWL_wt_star {p : ℝ} (hp1 : p < 1) (ρ : X → Option Bool) (S : Finset X) (g : X → Bool)
    (hS : ∀ e ∈ S, ρ e = none) :
    restrictionWeight p ρ = (2 * p / (1 - p)) ^ S.card * restrictionWeight p (SWL_setTo ρ S g) := by
  unfold restrictionWeight
  have : ∀ e, starWeight p (ρ e) =
      (if e ∈ S then 2 * p / (1 - p) else 1) * starWeight p (SWL_setTo ρ S g e) := by
    intro e
    by_cases he : e ∈ S
    · simp only [he, if_true, SWL_setTo, hS e he, starWeight]
      have : (1 - p) ≠ 0 := by linarith
      field_simp
    · simp [he, SWL_setTo]
  rw [Finset.prod_congr rfl (fun e _ => this e), Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.univ_inter, Finset.prod_const]

lemma SWL_wt_const {p : ℝ} (ρ : X → Option Bool) (S : Finset X) (g : X → Bool)
    (hS : ∀ e ∈ S, ρ e ≠ none) :
    restrictionWeight p (SWL_setTo ρ S g) = restrictionWeight p ρ := by
  unfold restrictionWeight
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : e ∈ S
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (hS e he)
    simp [SWL_setTo, he, hb, starWeight]
  · simp [SWL_setTo, he]

lemma SWL_total {p : ℝ} : restrictionProb p (fun _ : X → Option Bool => True) = 1 := by
  unfold restrictionProb restrictionWeight
  simp only [if_true]
  rw [← Fintype.prod_sum (fun (_ : X) (o : Option Bool) => starWeight p o)]
  have : ∑ o : Option Bool, starWeight p o = 1 := by
    simp [Fintype.sum_option, starWeight]; ring
  simp [this]


lemma SWL_step2 {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2) {μ : ℝ} (hμ : 0 ≤ μ)
    (L : List (Finset (X × Bool)))
    (ih : ∀ (t : ℕ) (U : (X → Option Bool) → Prop), SWL_up U →
      restrictionProb p (fun ρ => U ρ ∧ t ≤ SWL_cd L ρ) ≤ μ ^ t * restrictionProb p U)
    (T : Finset (X × Bool)) (hc : SWL_cons T) (S P : Finset X)
    (U : (X → Option Bool) → Prop) (hU : SWL_up U) (t' : ℕ) :
    restrictionProb p (fun ρ => U ρ ∧ ¬ SWL_fals T ρ ∧ SWL_stars T ρ = S ∧
        t' ≤ SWL_cd L (SWL_setTo ρ S (fun e => decide (e ∈ P))))
      ≤ (2 * p / (1 - p)) ^ S.card * (μ ^ t' *
          restrictionProb p (fun ρ => U ρ ∧ SWL_sat T ρ)) := by
  have hp1' : p ≤ 1 := by linarith
  have hp1'' : p < 1 := by linarith
  set g : X → Bool := fun e => decide (e ∈ P) with hg
  set σ := SWL_sig T
  set E : (X → Option Bool) → Prop := fun ρ => U ρ ∧ ¬ SWL_fals T ρ ∧ SWL_stars T ρ = S ∧
        t' ≤ SWL_cd L (SWL_setTo ρ S g) with hE
  set U' : (X → Option Bool) → Prop := fun ρ =>
    (U (SWL_setTo ρ S σ) ∧ SWL_sat T (SWL_setTo ρ S σ)) ∧ ∀ e ∈ S, ρ e = some (g e) with hU'
  have hstar : ∀ ρ, E ρ → ∀ e ∈ S, ρ e = none := by
    intro ρ hρ e he
    rw [← hρ.2.2.1] at he
    simp only [SWL_stars, Finset.mem_filter] at he
    exact he.2
  have hlam : 0 ≤ 2 * p / (1 - p) := div_nonneg (by linarith) (by linarith)
  have hU'up : SWL_up U' := by
    intro ρ ρ' h hr
    have hr' : ∀ e, SWL_setTo ρ S σ e ≠ none → SWL_setTo ρ' S σ e = SWL_setTo ρ S σ e := by
      intro e he
      by_cases heS : e ∈ S
      · simp [SWL_setTo, heS]
      · simp only [SWL_setTo, heS, if_false] at he ⊢; exact hr e he
    refine ⟨⟨hU _ _ h.1.1 hr', SWL_up_sat T _ _ h.1.2 hr'⟩, ?_⟩
    intro e he
    rw [hr e (by simp [h.2 e he]), h.2 e he]
  have hsetset : ∀ ρ, SWL_setTo (SWL_setTo ρ S g) S σ = SWL_setTo ρ S σ := by
    intro ρ; funext e; by_cases he : e ∈ S <;> simp [SWL_setTo, he]
  calc restrictionProb p E
      = ∑ ρ, if E ρ then (2 * p / (1 - p)) ^ S.card *
          restrictionWeight p (SWL_setTo ρ S g) else 0 := by
        unfold restrictionProb
        apply Finset.sum_congr rfl
        intro ρ _
        by_cases h : E ρ
        · simp only [h, if_true]; exact SWL_wt_star hp1'' ρ S g (hstar ρ h)
        · simp only [h, if_false]
    _ = (2 * p / (1 - p)) ^ S.card *
          ∑ ρ, if E ρ then restrictionWeight p (SWL_setTo ρ S g) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ _
        split_ifs <;> simp
    _ ≤ (2 * p / (1 - p)) ^ S.card *
          restrictionProb p (fun ρ => U' ρ ∧ t' ≤ SWL_cd L ρ) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlam _)
        unfold restrictionProb
        apply SWL_inj_sum E _ (fun ρ => SWL_setTo ρ S g) _ (SWL_wt_nonneg hp hp1')
        · intro a b ha hb hab
          funext e
          by_cases he : e ∈ S
          · rw [hstar a ha e he, hstar b hb e he]
          · have := congrFun hab e
            simpa [SWL_setTo, he] using this
        · intro ρ hρ
          refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hρ.2.2.2⟩
          · rw [hsetset]
            apply hU ρ _ hρ.1
            intro e he
            by_cases heS : e ∈ S
            · exact absurd (hstar ρ hρ e heS) he
            · simp [SWL_setTo, heS]
          · rw [hsetset]
            intro l hl
            by_cases heS : l.1 ∈ S
            · simp [SWL_setTo, heS, σ, SWL_sig_eq hc hl]
            · simp only [SWL_setTo, heS, if_false]
              have hn : ρ l.1 ≠ none := by
                intro hn; apply heS; rw [← hρ.2.2.1]
                simp only [SWL_stars, SWL_vars, Finset.mem_filter, Finset.mem_image]
                exact ⟨⟨l, hl, rfl⟩, hn⟩
              obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hn
              rw [hb]
              have hf := hρ.2.1
              by_contra hne
              apply hf
              refine ⟨l, hl, ?_⟩
              rw [hb]
              cases b <;> cases h2 : l.2 <;> simp_all
          · intro e he; simp [SWL_setTo, he]
    _ ≤ (2 * p / (1 - p)) ^ S.card * (μ ^ t' * restrictionProb p U') := by
        apply mul_le_mul_of_nonneg_left (ih t' U' hU'up) (pow_nonneg hlam _)
    _ ≤ (2 * p / (1 - p)) ^ S.card * (μ ^ t' *
          restrictionProb p (fun ρ => U ρ ∧ SWL_sat T ρ)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlam _)
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hμ _)
        have e1 : restrictionProb p U' =
            ∑ ρ, if U' ρ then restrictionWeight p (SWL_setTo ρ S σ) else 0 := by
          unfold restrictionProb
          apply Finset.sum_congr rfl
          intro ρ _
          by_cases h : U' ρ
          · simp only [h, if_true]
            rw [SWL_wt_const ρ S σ (fun e he => by simp [h.2 e he])]
          · simp only [h, if_false]
        rw [e1]
        unfold restrictionProb
        apply SWL_inj_sum U' _ (fun ρ => SWL_setTo ρ S σ) _ (SWL_wt_nonneg hp hp1')
        · intro a b ha hb hab
          funext e
          by_cases he : e ∈ S
          · rw [ha.2 e he, hb.2 e he]
          · have := congrFun hab e
            simpa [SWL_setTo, he] using this
        · intro ρ hρ; exact hρ.1

lemma SWL_step1 {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset (X × Bool)) (hc : SWL_cons T)
    (L : List (Finset (X × Bool))) (U : (X → Option Bool) → Prop) (t : ℕ) (ht : 1 ≤ t) :
    restrictionProb p (fun ρ => U ρ ∧ ¬ SWL_fals T ρ ∧ t ≤ SWL_cd (T :: L) ρ) ≤
      ∑ S ∈ (SWL_vars T).powerset, if S = ∅ then 0 else ∑ P ∈ S.powerset,
        restrictionProb p (fun ρ => U ρ ∧ ¬ SWL_fals T ρ ∧ SWL_stars T ρ = S ∧
          t - S.card ≤ SWL_cd L (SWL_setTo ρ S (fun e => decide (e ∈ P)))) := by
  unfold restrictionProb
  set b : Finset X → Finset X → (X → Option Bool) → ℝ := fun S P ρ =>
    if (U ρ ∧ ¬ SWL_fals T ρ ∧ SWL_stars T ρ = S ∧
          t - S.card ≤ SWL_cd L (SWL_setTo ρ S (fun e => decide (e ∈ P))))
    then restrictionWeight p ρ else 0 with hb
  have hbnn : ∀ S P ρ, 0 ≤ b S P ρ := by
    intro S P ρ; simp only [hb]; split_ifs
    · exact SWL_wt_nonneg hp hp1 ρ
    · exact le_rfl
  have key : (∑ ρ, if (U ρ ∧ ¬ SWL_fals T ρ ∧ t ≤ SWL_cd (T :: L) ρ) then restrictionWeight p ρ else 0)
      ≤ ∑ S ∈ (SWL_vars T).powerset, if S = ∅ then 0 else ∑ P ∈ S.powerset, ∑ ρ, b S P ρ := by
    calc
      _ ≤ ∑ ρ, ∑ S ∈ (SWL_vars T).powerset, if S = ∅ then 0 else ∑ P ∈ S.powerset, b S P ρ := by
        apply Finset.sum_le_sum
        intro ρ _
        have hnn : 0 ≤ ∑ S ∈ (SWL_vars T).powerset,
            if S = ∅ then 0 else ∑ P ∈ S.powerset, b S P ρ := by
          apply Finset.sum_nonneg; intro S _; split_ifs
          · exact le_rfl
          · exact Finset.sum_nonneg (fun P _ => hbnn S P ρ)
        by_cases hE : U ρ ∧ ¬ SWL_fals T ρ ∧ t ≤ SWL_cd (T :: L) ρ
        · simp only [hE]
          obtain ⟨hUρ, hf, ht'⟩ := hE
          set S0 := SWL_stars T ρ with hS0
          have hS0e : S0 ≠ ∅ := by
            intro h0
            simp only [SWL_cd, hc, hf, ← hS0, h0, not_true_eq_false,
              if_false, if_true] at ht'
            omega
          have hcd : SWL_cd (T :: L) ρ = S0.card + S0.powerset.sup
              (fun P => SWL_cd L (SWL_setTo ρ S0 (fun e => decide (e ∈ P)))) := by
            simp only [SWL_cd, hc, hf, ← hS0, hS0e, not_true_eq_false, if_false]
          obtain ⟨P0, hP0, hsup⟩ := Finset.exists_mem_eq_sup S0.powerset
            ⟨∅, Finset.empty_mem_powerset _⟩
            (fun P => SWL_cd L (SWL_setTo ρ S0 (fun e => decide (e ∈ P))))
          have hS0mem : S0 ∈ (SWL_vars T).powerset :=
            Finset.mem_powerset.mpr (Finset.filter_subset _ _)
          have hbval : b S0 P0 ρ = restrictionWeight p ρ := by
            simp only [hb]
            rw [if_pos]
            refine ⟨hUρ, hf, rfl, ?_⟩
            rw [hcd, hsup] at ht'
            omega
          calc restrictionWeight p ρ = b S0 P0 ρ := hbval.symm
            _ ≤ ∑ P ∈ S0.powerset, b S0 P ρ :=
                Finset.single_le_sum (fun P _ => hbnn S0 P ρ) hP0
            _ = (if S0 = ∅ then 0 else ∑ P ∈ S0.powerset, b S0 P ρ) := by simp [hS0e]
            _ ≤ _ := Finset.single_le_sum (f := fun S =>
                  if S = ∅ then 0 else ∑ P ∈ S.powerset, b S P ρ)
                  (fun S _ => by
                    split_ifs
                    · exact le_rfl
                    · exact Finset.sum_nonneg (fun P _ => hbnn S P ρ)) hS0mem
        · simp only [hE, if_false]; exact hnn
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : S = ∅
        · simp [hS]
        · simp only [hS, if_false]
          rw [Finset.sum_comm]
  convert key

lemma SWL_geom (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (if m = 0 then (0 : ℝ) else (1 / 2) ^ m) = 1 - (1 / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.succ_ne_zero, if_false, pow_succ]
    ring

lemma SWL_step3 (lam μ V : ℝ) (w k t : ℕ) (hk : k ≤ w) (hlam : 0 ≤ lam) (hμ0 : 0 ≤ μ)
    (hμ1 : μ ≤ 1) (hμ : μ = 4 * w * lam) (hV : 0 ≤ V) :
    ∑ m ∈ Finset.range (k + 1), k.choose m •
      (if m = 0 then (0 : ℝ) else (2 : ℝ) ^ m * (lam ^ m * (μ ^ (t - m) * V))) ≤ μ ^ t * V := by
  calc _ ≤ ∑ m ∈ Finset.range (k + 1), (if m = 0 then (0 : ℝ) else (1 / 2) ^ m) * (μ ^ t * V) := by
        apply Finset.sum_le_sum
        intro m _
        rw [nsmul_eq_mul]
        by_cases hm : m = 0
        · simp [hm]
        simp only [hm, if_false]
        have hc : (k.choose m : ℝ) ≤ (w : ℝ) ^ m := by
          have h1 : (k.choose m : ℝ) ≤ (k : ℝ) ^ m := by exact_mod_cast Nat.choose_le_pow k m
          exact h1.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hk) m)
        have hpow : μ ^ m * μ ^ (t - m) ≤ μ ^ t := by
          rw [← pow_add]; exact pow_le_pow_of_le_one hμ0 hμ1 (by omega)
        have hnn : 0 ≤ (2 : ℝ) ^ m * (lam ^ m * (μ ^ (t - m) * V)) := by positivity
        calc (k.choose m : ℝ) * ((2 : ℝ) ^ m * (lam ^ m * (μ ^ (t - m) * V)))
            ≤ (w : ℝ) ^ m * ((2 : ℝ) ^ m * (lam ^ m * (μ ^ (t - m) * V))) :=
              mul_le_mul_of_nonneg_right hc hnn
          _ = (1 / 2) ^ m * ((μ ^ m * μ ^ (t - m)) * V) := by
              have h2 : (w : ℝ) ^ m * ((2 : ℝ) ^ m * lam ^ m) = (1 / 2) ^ m * μ ^ m := by
                rw [hμ, ← mul_pow, ← mul_pow, ← mul_pow]; congr 1; ring
              calc (w : ℝ) ^ m * ((2 : ℝ) ^ m * (lam ^ m * (μ ^ (t - m) * V)))
                  = ((w : ℝ) ^ m * ((2 : ℝ) ^ m * lam ^ m)) * (μ ^ (t - m) * V) := by ring
                _ = _ := by rw [h2]; ring
          _ ≤ (1 / 2) ^ m * (μ ^ t * V) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right hpow hV
    _ = (∑ m ∈ Finset.range (k + 1), (if m = 0 then (0 : ℝ) else (1 / 2) ^ m)) * (μ ^ t * V) := by
        rw [Finset.sum_mul]
    _ ≤ 1 * (μ ^ t * V) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [SWL_geom]
        have : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
        linarith
    _ = μ ^ t * V := one_mul _

lemma SWL_main {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2) (w : ℕ) {μ : ℝ}
    (hμ : μ = 4 * w * (2 * p / (1 - p))) (hμ1 : μ ≤ 1)
    (L : List (Finset (X × Bool))) (hL : ∀ T ∈ L, T.card ≤ w) :
    ∀ (t : ℕ) (U : (X → Option Bool) → Prop), SWL_up U →
      restrictionProb p (fun ρ => U ρ ∧ t ≤ SWL_cd L ρ) ≤ μ ^ t * restrictionProb p U := by
  have hp1' : p ≤ 1 := by linarith
  have hlam : 0 ≤ 2 * p / (1 - p) := div_nonneg (by linarith) (by linarith)
  have hμ0 : 0 ≤ μ := by rw [hμ]; positivity
  have zero_case : ∀ (L : List (Finset (X × Bool))) (U : (X → Option Bool) → Prop),
      restrictionProb p (fun ρ => U ρ ∧ 0 ≤ SWL_cd L ρ) ≤ μ ^ 0 * restrictionProb p U := by
    intro L U
    rw [pow_zero, one_mul]
    exact SWL_prob_mono hp hp1' (fun ρ h => h.1)
  induction L with
  | nil =>
    intro t U _
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact zero_case [] U
    · have : restrictionProb p (fun ρ => U ρ ∧ t ≤ SWL_cd [] ρ) = 0 := by
        unfold restrictionProb
        apply Finset.sum_eq_zero
        intro ρ _
        have : ¬ (U ρ ∧ t ≤ SWL_cd [] ρ) := by simp [SWL_cd]; omega
        simp [this]
      rw [this]
      exact mul_nonneg (pow_nonneg hμ0 _) (SWL_prob_nonneg hp hp1' _)
  | cons T L ih =>
    have ih := ih (fun T hT => hL T (List.mem_cons_of_mem _ hT))
    intro t U hU
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact zero_case _ U
    by_cases hc : SWL_cons T
    swap
    · rw [SWL_prob_congr (E' := fun ρ => U ρ ∧ t ≤ SWL_cd L ρ)
        (fun ρ => by simp only [SWL_cd, hc, not_false_eq_true, if_true])]
      exact ih t U hU
    have hTw : (SWL_vars T).card ≤ w := (Finset.card_image_le).trans (hL T List.mem_cons_self)
    rw [SWL_prob_split p _ (SWL_fals T)]
    have h1 : restrictionProb p (fun ρ => (U ρ ∧ t ≤ SWL_cd (T :: L) ρ) ∧ SWL_fals T ρ) ≤
        μ ^ t * restrictionProb p (fun ρ => U ρ ∧ SWL_fals T ρ) := by
      rw [SWL_prob_congr (E' := fun ρ => (U ρ ∧ SWL_fals T ρ) ∧ t ≤ SWL_cd L ρ)]
      · exact ih t _ (SWL_up_and hU (SWL_up_fals T))
      · intro ρ
        by_cases hf : SWL_fals T ρ
        · simp only [SWL_cd, hc, hf, not_true_eq_false, if_false, if_true]; tauto
        · simp [hf]
    have h2 : restrictionProb p (fun ρ => (U ρ ∧ t ≤ SWL_cd (T :: L) ρ) ∧ ¬ SWL_fals T ρ) ≤
        μ ^ t * restrictionProb p (fun ρ => U ρ ∧ SWL_sat T ρ) := by
      rw [SWL_prob_congr (E' := fun ρ => U ρ ∧ ¬ SWL_fals T ρ ∧ t ≤ SWL_cd (T :: L) ρ)
        (fun ρ => by tauto)]
      refine (SWL_step1 hp hp1' T hc L U t ht).trans ?_
      set V := restrictionProb p (fun ρ => U ρ ∧ SWL_sat T ρ)
      have hV : 0 ≤ V := SWL_prob_nonneg hp hp1' _
      calc _ ≤ ∑ S ∈ (SWL_vars T).powerset, (fun m : ℕ =>
              if m = 0 then (0 : ℝ) else (2 : ℝ) ^ m * ((2 * p / (1 - p)) ^ m * (μ ^ (t - m) * V)))
              S.card := by
            apply Finset.sum_le_sum
            intro S _
            by_cases hS : S = ∅
            · simp [hS]
            have hSc : S.card ≠ 0 := by rwa [Ne, Finset.card_eq_zero]
            simp only [hS, hSc, if_false]
            calc _ ≤ ∑ P ∈ S.powerset, (2 * p / (1 - p)) ^ S.card * (μ ^ (t - S.card) * V) :=
                  Finset.sum_le_sum (fun P _ =>
                    SWL_step2 hp hp1 hμ0 L ih T hc S P U hU (t - S.card))
              _ = _ := by
                  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]; push_cast; ring
        _ = _ := Finset.sum_powerset_apply_card (fun m : ℕ =>
              if m = 0 then (0 : ℝ) else (2 : ℝ) ^ m * ((2 * p / (1 - p)) ^ m * (μ ^ (t - m) * V)))
        _ ≤ μ ^ t * V := SWL_step3 _ μ V w _ t hTw hlam hμ0 hμ1 hμ hV
    calc _ ≤ μ ^ t * restrictionProb p (fun ρ => U ρ ∧ SWL_fals T ρ) +
          μ ^ t * restrictionProb p (fun ρ => U ρ ∧ SWL_sat T ρ) := add_le_add h1 h2
      _ = μ ^ t * (restrictionProb p (fun ρ => U ρ ∧ SWL_fals T ρ) +
          restrictionProb p (fun ρ => U ρ ∧ SWL_sat T ρ)) := by ring
      _ ≤ μ ^ t * restrictionProb p U := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hμ0 _)
          apply SWL_prob_disj p hp hp1' U
          intro ρ ⟨l, hl, h1⟩ h2
          rw [h2 l hl] at h1
          cases h : l.2 <;> simp_all

end counting

end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution {X : Type} [Fintype X] (w t : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (F : Finset (Finset (X × Bool))) (hF : ∀ T ∈ F, T.card ≤ w) :
    restrictionProb p (fun ρ => ¬ DTDepthLE t (restrictFn ρ (dnfValue F))) ≤
      (16 * p * (w : ℝ)) ^ t := by
  have hp1 : p ≤ 1 := by linarith
  set μ : ℝ := 4 * w * (2 * p / (1 - p)) with hμ
  have hμ0 : 0 ≤ μ := by
    rw [hμ]; exact mul_nonneg (by positivity) (div_nonneg (by linarith) (by linarith))
  have hμ16 : μ ≤ 16 * p * w := by
    rw [hμ]
    have h1 : 0 < 1 - p := by linarith
    rw [show (4 : ℝ) * w * (2 * p / (1 - p)) = (8 * p * w) / (1 - p) by field_simp; ring]
    rw [div_le_iff₀ h1]
    have : 0 ≤ p * (w : ℝ) := mul_nonneg hp (Nat.cast_nonneg _)
    nlinarith
  have hle1 : restrictionProb p (fun ρ => ¬ DTDepthLE t (restrictFn ρ (dnfValue F))) ≤ 1 := by
    rw [← SWL_total (X := X) (p := p)]
    exact SWL_prob_mono hp hp1 (fun _ _ => trivial)
  by_cases hμ1 : μ ≤ 1
  · have hd : dnfValue F = SWL_dnf F.toList := by
      funext x; simp [dnfValue, SWL_dnf]
    have hL : ∀ T ∈ F.toList, T.card ≤ w := fun T hT => hF T (Finset.mem_toList.mp hT)
    calc restrictionProb p (fun ρ => ¬ DTDepthLE t (restrictFn ρ (dnfValue F)))
        ≤ restrictionProb p (fun ρ => True ∧ t ≤ SWL_cd F.toList ρ) := by
          apply SWL_prob_mono hp hp1
          intro ρ hρ
          refine ⟨trivial, ?_⟩
          by_contra hlt
          apply hρ
          rw [hd]
          exact SWL_dt_mono (SWL_dt_cd F.toList ρ) (by omega)
      _ ≤ μ ^ t * restrictionProb p (fun _ => True) :=
          SWL_main hp hp2 w hμ hμ1 F.toList hL t (fun _ => True) (fun _ _ _ _ => trivial)
      _ = μ ^ t := by rw [SWL_total, mul_one]
      _ ≤ (16 * p * (w : ℝ)) ^ t := pow_le_pow_left₀ hμ0 hμ16 t
  · push Not at hμ1
    exact hle1.trans (one_le_pow₀ (by linarith))

