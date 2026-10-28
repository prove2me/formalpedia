-- Prove2me | solution 1 for NonsmoothLojasiewicz.Continuous.tarski_seidenberg_parametric
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T06:05:44.77499+00:00
-- url     : https://prove2.me/submissions/f660744c-7747-44c6-a829-668cc6cb99bb

import Mathlib
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Filter Topology
set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-! SubanalyticLib CS-4: Thom's lemma (Bochnak–Coste–Roy, Real Algebraic Geometry, Prop. 2.5.4 /
Basu–Pollack–Roy Lemma 2.37). For a finite family of real polynomials closed under derivation,
every sign condition defines an order-connected set that is a point (subsingleton) or open,
i.e. empty, a point or an open interval. -/

open Polynomial Set

set_option linter.unusedSectionVars false

namespace SubanalyticLib

/-- The realization of the sign condition `ν` on the family `PP`. -/
def signSet (PP : Finset ℝ[X]) (ν : ℝ[X] → SignType) : Set ℝ :=
  {x : ℝ | ∀ p ∈ PP, SignType.sign (p.eval x) = ν p}

/-- Derivative-closed family. -/
def DerivClosed (PP : Finset ℝ[X]) : Prop := ∀ p ∈ PP, derivative p ∈ PP

theorem deriv_eval_poly (p : ℝ[X]) (x : ℝ) :
    deriv (fun y => p.eval y) x = (derivative p).eval x := Polynomial.deriv p

/-- A sign condition on a monotone function cuts an order-connected set to an order-connected set. -/
theorem ordConn_of_monotoneOn {A' : Set ℝ} (hA' : A'.OrdConnected) {f : ℝ → ℝ}
    (hm : MonotoneOn f A' ∨ AntitoneOn f A') (t : SignType) :
    (A' ∩ {x | SignType.sign (f x) = t}).OrdConnected := by
  constructor
  intro x hx z hz y hy
  have hyA : y ∈ A' := hA'.out hx.1 hz.1 hy
  refine ⟨hyA, ?_⟩
  have h1 : SignType.sign (f x) = t := hx.2
  have h2 : SignType.sign (f z) = t := hz.2
  show SignType.sign (f y) = t
  have hb : (f x ≤ f y ∧ f y ≤ f z) ∨ (f y ≤ f x ∧ f z ≤ f y) := by
    rcases hm with hm | hm
    · exact Or.inl ⟨hm hx.1 hyA hy.1, hm hyA hz.1 hy.2⟩
    · exact Or.inr ⟨hm hx.1 hyA hy.1, hm hyA hz.1 hy.2⟩
  rcases t with _ | _ | _
  · have e1 : f x = 0 := sign_eq_zero_iff.mp h1
    have e2 : f z = 0 := sign_eq_zero_iff.mp h2
    apply sign_eq_zero_iff.mpr
    rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> exact le_antisymm (by linarith) (by linarith)
  · rw [SignType.neg_eq_neg_one, sign_eq_neg_one_iff] at h1 h2 ⊢
    rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith
  · rw [SignType.pos_eq_one, sign_eq_one_iff] at h1 h2 ⊢
    rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith

/-- One step: `A'` order-connected, `p` with `p'` of constant sign `s` on `A'`. -/
theorem thom_step {A' : Set ℝ} (hA' : A'.OrdConnected) (hA'o : A'.Subsingleton ∨ IsOpen A')
    (p : ℝ[X]) (s : SignType) (hs : ∀ x ∈ A', SignType.sign ((derivative p).eval x) = s)
    (t : SignType) :
    (A' ∩ {x | SignType.sign (p.eval x) = t}).OrdConnected ∧
      ((A' ∩ {x | SignType.sign (p.eval x) = t}).Subsingleton ∨
        IsOpen (A' ∩ {x | SignType.sign (p.eval x) = t})) := by
  have hconv : Convex ℝ A' := hA'.convex
  have hcont : ContinuousOn (fun y => p.eval y) A' := p.continuous.continuousOn
  have hint : ∀ x ∈ interior A', x ∈ A' := fun x hx => interior_subset hx
  have hdiff : DifferentiableOn ℝ (fun y => p.eval y) (interior A') :=
    p.differentiable.differentiableOn
  -- the subsingleton case is immediate
  have hsub : A'.Subsingleton → (A' ∩ {x | SignType.sign (p.eval x) = t}).Subsingleton :=
    fun h => h.anti inter_subset_left
  -- openness for strict signs
  have hopen : IsOpen A' → t ≠ 0 → IsOpen (A' ∩ {x | SignType.sign (p.eval x) = t}) := by
    intro ho ht
    rcases t with _ | _ | _
    · exact absurd rfl ht
    · have : {x : ℝ | SignType.sign (p.eval x) = SignType.neg} = (fun y => p.eval y) ⁻¹' Iio 0 := by
        ext x; simp [SignType.neg_eq_neg_one, sign_eq_neg_one_iff]
      rw [this]; exact ho.inter (isOpen_Iio.preimage p.continuous)
    · have : {x : ℝ | SignType.sign (p.eval x) = SignType.pos} = (fun y => p.eval y) ⁻¹' Ioi 0 := by
        ext x; simp [SignType.pos_eq_one, sign_eq_one_iff]
      rw [this]; exact ho.inter (isOpen_Ioi.preimage p.continuous)
  rcases s with _ | _ | _
  · -- p' = 0 on A': p constant on A'
    have hz : ∀ x ∈ A', (derivative p).eval x = 0 := by
      intro x hx; have := hs x hx; simpa [sign_eq_zero_iff] using this
    have hmono : MonotoneOn (fun y => p.eval y) A' :=
      monotoneOn_of_deriv_nonneg hconv hcont hdiff
        (fun x hx => by rw [deriv_eval_poly, hz x (hint x hx)])
    have hanti : AntitoneOn (fun y => p.eval y) A' :=
      antitoneOn_of_deriv_nonpos hconv hcont hdiff
        (fun x hx => by rw [deriv_eval_poly, hz x (hint x hx)])
    have hc : ∀ x ∈ A', ∀ y ∈ A', p.eval x = p.eval y := by
      intro x hx y hy
      rcases le_total x y with h | h
      · exact le_antisymm (hmono hx hy h) (hanti hx hy h)
      · exact le_antisymm (hanti hy hx h) (hmono hy hx h)
    by_cases hne : ∃ x₀ ∈ A', SignType.sign (p.eval x₀) = t
    · obtain ⟨x₀, hx₀, ht⟩ := hne
      have hA : A' ∩ {x | SignType.sign (p.eval x) = t} = A' := by
        ext x; constructor
        · exact fun h => h.1
        · intro hx; exact ⟨hx, by simp only [mem_setOf_eq]; rw [hc x hx x₀ hx₀]; exact ht⟩
      rw [hA]; exact ⟨hA', hA'o⟩
    · push Not at hne
      have hA : A' ∩ {x | SignType.sign (p.eval x) = t} = ∅ := by
        ext x; simp only [mem_empty_iff_false, iff_false]
        exact fun h => hne x h.1 h.2
      rw [hA]; exact ⟨ordConnected_empty, Or.inl subsingleton_empty⟩
  · -- p' < 0 on A': p strictly decreasing
    have hn : ∀ x ∈ A', (derivative p).eval x < 0 := by
      intro x hx; have := hs x hx; simpa [SignType.neg_eq_neg_one, sign_eq_neg_one_iff] using this
    have hsa : StrictAntiOn (fun y => p.eval y) A' :=
      strictAntiOn_of_deriv_neg hconv hcont (fun x hx => by rw [deriv_eval_poly]; exact hn x (hint x hx))
    refine ⟨ordConn_of_monotoneOn hA' (Or.inr hsa.antitoneOn) t, ?_⟩
    rcases hA'o with h | h
    · exact Or.inl (hsub h)
    · by_cases ht : t = 0
      · left; subst ht
        intro x hx y hy
        have e1 : p.eval x = 0 := by simpa [sign_eq_zero_iff] using hx.2
        have e2 : p.eval y = 0 := by simpa [sign_eq_zero_iff] using hy.2
        exact hsa.injOn hx.1 hy.1 (by simp only [e1, e2])
      · exact Or.inr (hopen h ht)
  · -- p' > 0 on A': p strictly increasing
    have hn : ∀ x ∈ A', 0 < (derivative p).eval x := by
      intro x hx; have := hs x hx; simpa [SignType.pos_eq_one, sign_eq_one_iff] using this
    have hsm : StrictMonoOn (fun y => p.eval y) A' :=
      strictMonoOn_of_deriv_pos hconv hcont (fun x hx => by rw [deriv_eval_poly]; exact hn x (hint x hx))
    refine ⟨ordConn_of_monotoneOn hA' (Or.inl hsm.monotoneOn) t, ?_⟩
    rcases hA'o with h | h
    · exact Or.inl (hsub h)
    · by_cases ht : t = 0
      · left; subst ht
        intro x hx y hy
        have e1 : p.eval x = 0 := by simpa [sign_eq_zero_iff] using hx.2
        have e2 : p.eval y = 0 := by simpa [sign_eq_zero_iff] using hy.2
        exact hsm.injOn hx.1 hy.1 (by simp only [e1, e2])
      · exact Or.inr (hopen h ht)

/-- **Thom's lemma.** -/
theorem eval_const {p : ℝ[X]} (h : p.natDegree = 0) (x : ℝ) : p.eval x = p.coeff 0 := by
  conv_lhs => rw [eq_C_of_natDegree_eq_zero h]
  simp

theorem thom : ∀ (n : ℕ) (PP : Finset ℝ[X]), PP.card ≤ n → DerivClosed PP → ∀ ν : ℝ[X] → SignType,
    (signSet PP ν).OrdConnected ∧ ((signSet PP ν).Subsingleton ∨ IsOpen (signSet PP ν)) := by
  intro n
  induction n with
  | zero =>
    intro PP hPP _ ν
    have : PP = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    have : signSet ∅ ν = univ := by ext x; simp [signSet]
    rw [this]; exact ⟨ordConnected_univ, Or.inr isOpen_univ⟩
  | succ n ih =>
    intro PP hPP hcl ν
    by_cases hconst : ∀ p ∈ PP, p.natDegree = 0
    · -- all constant: the sign set is ∅ or univ
      by_cases hall : ∀ p ∈ PP, SignType.sign (p.coeff 0) = ν p
      · have : signSet PP ν = univ := by
          ext x; simp only [signSet, mem_setOf_eq, mem_univ, iff_true]
          intro p hp
          rw [eval_const (hconst p hp)]; exact hall p hp
        rw [this]; exact ⟨ordConnected_univ, Or.inr isOpen_univ⟩
      · push Not at hall
        obtain ⟨p, hp, hne⟩ := hall
        have : signSet PP ν = ∅ := by
          ext x; simp only [signSet, mem_setOf_eq, mem_empty_iff_false, iff_false]
          intro h; apply hne
          have := h p hp
          rwa [eval_const (hconst p hp)] at this
        rw [this]; exact ⟨ordConnected_empty, Or.inl subsingleton_empty⟩
    · push Not at hconst
      obtain ⟨q, hq, hqd⟩ := hconst
      have hne : PP.Nonempty := ⟨q, hq⟩
      obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image PP natDegree hne
      have hpd : p.natDegree ≠ 0 := by
        have := hmax q hq; omega
      set PP' := PP.erase p with hPP'
      have hcard : PP'.card ≤ n := by
        rw [Finset.card_erase_of_mem hp]; omega
      have hdp : derivative p ∈ PP' := by
        refine Finset.mem_erase.mpr ⟨?_, hcl p hp⟩
        intro h
        have := natDegree_derivative_lt hpd
        rw [h] at this; exact lt_irrefl _ this
      have hcl' : DerivClosed PP' := by
        intro r hr
        obtain ⟨hrp, hrPP⟩ := Finset.mem_erase.mp hr
        refine Finset.mem_erase.mpr ⟨?_, hcl r hrPP⟩
        intro h
        by_cases hr0 : r.natDegree = 0
        · rw [derivative_of_natDegree_zero hr0] at h
          apply hpd; rw [← h]; simp
        · have h1 := natDegree_derivative_lt hr0
          have h2 := hmax r hrPP
          rw [h] at h1; omega
      obtain ⟨hA', hA'o⟩ := ih PP' hcard hcl' ν
      have hsplit : signSet PP ν = signSet PP' ν ∩ {x | SignType.sign (p.eval x) = ν p} := by
        ext x
        simp only [signSet, mem_setOf_eq, mem_inter_iff]
        constructor
        · intro h
          exact ⟨fun r hr => h r (Finset.mem_of_mem_erase hr), h p hp⟩
        · rintro ⟨h, hpx⟩ r hr
          by_cases hrp : r = p
          · subst hrp; exact hpx
          · exact h r (Finset.mem_erase.mpr ⟨hrp, hr⟩)
      rw [hsplit]
      exact thom_step hA' hA'o p (ν (derivative p)) (fun x hx => hx _ hdp) (ν p)

/-- Relaxed sign: `t` is `s` or `0`. -/
def Relax (s t : SignType) : Prop := t = s ∨ t = 0

/-- Realization of the relaxed (closed) sign condition. -/
def relaxSet (PP : Finset ℝ[X]) (ν : ℝ[X] → SignType) : Set ℝ :=
  {x : ℝ | ∀ p ∈ PP, Relax (ν p) (SignType.sign (p.eval x))}

theorem relax_iff (s : SignType) (v : ℝ) :
    Relax s (SignType.sign v) ↔ (s = 0 ∧ v = 0) ∨ (s = 1 ∧ 0 ≤ v) ∨ (s = -1 ∧ v ≤ 0) := by
  rcases lt_trichotomy v 0 with h | h | h
  · rw [sign_neg h]
    have h1 : ¬ v = 0 := h.ne
    have h2 : ¬ 0 ≤ v := not_le.mpr h
    rcases s with _ | _ | _ <;> simp [Relax, h1, h2, h.le] <;> decide
  · subst h
    rw [sign_zero]
    rcases s with _ | _ | _ <;> simp [Relax] <;> decide
  · rw [sign_pos h]
    have h1 : ¬ v = 0 := h.ne'
    have h2 : ¬ v ≤ 0 := not_le.mpr h
    rcases s with _ | _ | _ <;> simp [Relax, h1, h2, h.le] <;> decide

theorem ordConn_relax_of_monotoneOn {A' : Set ℝ} (hA' : A'.OrdConnected) {f : ℝ → ℝ}
    (hm : MonotoneOn f A' ∨ AntitoneOn f A') (t : SignType) :
    (A' ∩ {x | Relax t (SignType.sign (f x))}).OrdConnected := by
  constructor
  intro x hx z hz y hy
  have hyA : y ∈ A' := hA'.out hx.1 hz.1 hy
  refine ⟨hyA, ?_⟩
  have h1 : Relax t (SignType.sign (f x)) := hx.2
  have h2 : Relax t (SignType.sign (f z)) := hz.2
  show Relax t (SignType.sign (f y))
  rw [relax_iff] at h1 h2 ⊢
  have hb : (f x ≤ f y ∧ f y ≤ f z) ∨ (f y ≤ f x ∧ f z ≤ f y) := by
    rcases hm with hm | hm
    · exact Or.inl ⟨hm hx.1 hyA hy.1, hm hyA hz.1 hy.2⟩
    · exact Or.inr ⟨hm hx.1 hyA hy.1, hm hyA hz.1 hy.2⟩
  rcases h1 with ⟨e1, f1⟩ | ⟨e1, f1⟩ | ⟨e1, f1⟩ <;>
  rcases h2 with ⟨e2, f2⟩ | ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
  first
  | (exact absurd (e1.symm.trans e2) (by decide))
  | (left; refine ⟨e1, ?_⟩; rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      exact le_antisymm (by linarith) (by linarith))
  | (right; left; refine ⟨e1, ?_⟩; rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith)
  | (right; right; refine ⟨e1, ?_⟩; rcases hb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> linarith)

/-- **Relaxed Thom lemma**: closed sign conditions on a derivative-closed family are intervals. -/
theorem thom_relax : ∀ (n : ℕ) (PP : Finset ℝ[X]), PP.card ≤ n → DerivClosed PP →
    ∀ ν : ℝ[X] → SignType, (relaxSet PP ν).OrdConnected := by
  intro n
  induction n with
  | zero =>
    intro PP hPP _ ν
    have : PP = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    have : relaxSet ∅ ν = univ := by ext x; simp [relaxSet]
    rw [this]; exact ordConnected_univ
  | succ n ih =>
    intro PP hPP hcl ν
    by_cases hconst : ∀ p ∈ PP, p.natDegree = 0
    · by_cases hall : ∀ p ∈ PP, Relax (ν p) (SignType.sign (p.coeff 0))
      · have : relaxSet PP ν = univ := by
          ext x; simp only [relaxSet, mem_setOf_eq, mem_univ, iff_true]
          intro p hp
          rw [eval_const (hconst p hp)]; exact hall p hp
        rw [this]; exact ordConnected_univ
      · push Not at hall
        obtain ⟨p, hp, hne⟩ := hall
        have : relaxSet PP ν = ∅ := by
          ext x; simp only [relaxSet, mem_setOf_eq, mem_empty_iff_false, iff_false]
          intro h; apply hne
          have := h p hp
          rwa [eval_const (hconst p hp)] at this
        rw [this]; exact ordConnected_empty
    · push Not at hconst
      obtain ⟨q, hq, hqd⟩ := hconst
      obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image PP natDegree ⟨q, hq⟩
      have hpd : p.natDegree ≠ 0 := by
        have := hmax q hq; omega
      set PP' := PP.erase p with hPP'
      have hcard : PP'.card ≤ n := by
        rw [Finset.card_erase_of_mem hp]; omega
      have hdp : derivative p ∈ PP' := by
        refine Finset.mem_erase.mpr ⟨?_, hcl p hp⟩
        intro h
        have := natDegree_derivative_lt hpd
        rw [h] at this; exact lt_irrefl _ this
      have hcl' : DerivClosed PP' := by
        intro r hr
        obtain ⟨hrp, hr𝒫⟩ := Finset.mem_erase.mp hr
        refine Finset.mem_erase.mpr ⟨?_, hcl r hr𝒫⟩
        intro h
        by_cases hr0 : r.natDegree = 0
        · rw [derivative_of_natDegree_zero hr0] at h
          apply hpd; rw [← h]; simp
        · have h1 := natDegree_derivative_lt hr0
          have h2 := hmax r hr𝒫
          rw [h] at h1; omega
      have hA' := ih PP' hcard hcl' ν
      have hsplit : relaxSet PP ν = relaxSet PP' ν ∩ {x | Relax (ν p) (SignType.sign (p.eval x))} := by
        ext x
        simp only [relaxSet, mem_setOf_eq, mem_inter_iff]
        constructor
        · intro h
          exact ⟨fun r hr => h r (Finset.mem_of_mem_erase hr), h p hp⟩
        · rintro ⟨h, hpx⟩ r hr
          by_cases hrp : r = p
          · subst hrp; exact hpx
          · exact h r (Finset.mem_erase.mpr ⟨hrp, hr⟩)
      rw [hsplit]
      -- p is monotone or antitone on the relaxed set of PP'
      have hconv : Convex ℝ (relaxSet PP' ν) := hA'.convex
      have hcont : ContinuousOn (fun y => p.eval y) (relaxSet PP' ν) := p.continuous.continuousOn
      have hdiff : DifferentiableOn ℝ (fun y => p.eval y) (interior (relaxSet PP' ν)) :=
        p.differentiable.differentiableOn
      have hder : ∀ x ∈ relaxSet PP' ν, Relax (ν (derivative p))
          (SignType.sign ((derivative p).eval x)) := fun x hx => hx _ hdp
      have hm : MonotoneOn (fun y => p.eval y) (relaxSet PP' ν) ∨
          AntitoneOn (fun y => p.eval y) (relaxSet PP' ν) := by
        rcases h : ν (derivative p) with _ | _ | _
        · left
          refine monotoneOn_of_deriv_nonneg hconv hcont hdiff (fun x hx => ?_)
          have := hder x (interior_subset hx)
          rw [h, relax_iff] at this
          rw [deriv_eval_poly]
          rcases this with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e, _⟩
          · rw [e]
          · exact absurd e (by decide)
          · exact absurd e (by decide)
        · right
          refine antitoneOn_of_deriv_nonpos hconv hcont hdiff (fun x hx => ?_)
          have := hder x (interior_subset hx)
          rw [h, relax_iff] at this
          rw [deriv_eval_poly]
          rcases this with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, e⟩
          · exact absurd e (by decide)
          · exact absurd e (by decide)
          · exact e
        · left
          refine monotoneOn_of_deriv_nonneg hconv hcont hdiff (fun x hx => ?_)
          have := hder x (interior_subset hx)
          rw [h, relax_iff] at this
          rw [deriv_eval_poly]
          rcases this with ⟨e, _⟩ | ⟨_, e⟩ | ⟨e, _⟩
          · exact absurd e (by decide)
          · exact e
          · exact absurd e (by decide)
      exact ordConn_relax_of_monotoneOn hA' hm (ν p)

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-b (part 2): ends of a sign-condition cell.
Appended to L4t_Thom.lean (uses `signSet`, `relaxSet`, `Relax`, `relax_iff`, `thom`, `thom_relax`).
* eventual signs of a real polynomial at `±∞` (`eventually_sign_atTop/atBot`);
* indexed sign sets `iSign Q ev μ` / `iRelax Q ev μ` and their transfer to `signSet`/`relaxSet`;
* `iSign` eventually contains `[c,∞)` iff every code is the sign at `+∞` (`eventually_mem_iSign_atTop_iff`);
* closure of a nonempty cell = its relaxed set (`mem_closure_of_iRelax`, `closure_iSign_subset`);
* realized signs of a strictly monotone continuous function on an open interval, read off at the
  finite endpoints and at the infinite ends (`realized_pos_iff`, `realized_zero_iff`). -/

open Polynomial Set Filter Topology

namespace SubanalyticLib

theorem eventually_sign_atTop (p : ℝ[X]) :
    ∀ᶠ x in atTop, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  rcases le_or_gt p.degree 0 with h | h
  · have hp := eq_C_of_degree_le_zero h
    refine Eventually.of_forall fun x => ?_
    rw [hp]; simp
  · rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt h)) with hl | hl
    · have := Polynomial.tendsto_atBot_of_leadingCoeff_nonpos p h hl.le
      filter_upwards [this.eventually (eventually_lt_atBot 0)] with x hx
      rw [sign_neg hx, sign_neg hl]
    · have := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg p h hl.le
      filter_upwards [this.eventually (eventually_gt_atTop 0)] with x hx
      rw [sign_pos hx, sign_pos hl]

/-- Sign at `-∞` of `p` is the sign at `+∞` of `p(-X)`. -/
theorem eventually_sign_atBot (p : ℝ[X]) :
    ∀ᶠ x in atBot, SignType.sign (p.eval x) = SignType.sign (p.comp (-X)).leadingCoeff := by
  have h := tendsto_neg_atBot_atTop.eventually (eventually_sign_atTop (p.comp (-X)))
  filter_upwards [h] with x hx
  simpa [eval_comp] using hx

theorem leadingCoeff_comp_neg_X (p : ℝ[X]) :
    (p.comp (-X)).leadingCoeff = (-1) ^ p.natDegree * p.leadingCoeff := by
  rw [leadingCoeff_comp (by rw [natDegree_neg, natDegree_X]; exact one_ne_zero)]
  rw [leadingCoeff_neg, leadingCoeff_X, mul_comm]

section Indexed

variable {ι : Type*}

/-- Realization of a sign condition on an indexed family of polynomials. -/
def iSign (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) : Set ℝ :=
  {x : ℝ | ∀ i ∈ Q, SignType.sign ((ev i).eval x) = μ i}

/-- Realization of the relaxed sign condition on an indexed family. -/
def iRelax (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) : Set ℝ :=
  {x : ℝ | ∀ i ∈ Q, Relax (μ i) (SignType.sign ((ev i).eval x))}

/-- Indexed derivative closure. -/
def IDerivClosed (Q : Finset ι) (ev : ι → ℝ[X]) : Prop :=
  ∀ i ∈ Q, ∃ j ∈ Q, ev j = derivative (ev i)

theorem iSign_subset_iRelax (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) :
    iSign Q ev μ ⊆ iRelax Q ev μ := fun _ hx i hi => Or.inl (hx i hi)

theorem derivClosed_image {Q : Finset ι} {ev : ι → ℝ[X]} (h : IDerivClosed Q ev) :
    DerivClosed (Q.image ev) := by
  classical
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, hj, e⟩ := h i hi
  exact Finset.mem_image.mpr ⟨j, hj, e⟩

/-- Transfer: a nonempty indexed cell is the cell of the image family with the code read at a point. -/
theorem iSign_eq_signSet [DecidableEq ℝ[X]] {Q : Finset ι} {ev : ι → ℝ[X]} {μ : ι → SignType} {x₀ : ℝ}
    (h₀ : x₀ ∈ iSign Q ev μ) :
    iSign Q ev μ = signSet (Q.image ev) (fun p => SignType.sign (p.eval x₀)) := by
  ext x
  simp only [iSign, signSet, mem_setOf_eq, Finset.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro hx i hi; rw [hx i hi, h₀ i hi]
  · intro hx i hi; rw [hx i hi, h₀ i hi]

theorem iRelax_eq_relaxSet [DecidableEq ℝ[X]] {Q : Finset ι} {ev : ι → ℝ[X]} {μ : ι → SignType} {x₀ : ℝ}
    (h₀ : x₀ ∈ iSign Q ev μ) :
    iRelax Q ev μ = relaxSet (Q.image ev) (fun p => SignType.sign (p.eval x₀)) := by
  ext x
  simp only [iRelax, relaxSet, mem_setOf_eq, Finset.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro hx i hi; rw [h₀ i hi]; exact hx i hi
  · intro hx i hi; rw [← h₀ i hi]; exact hx i hi

/-- Thom's lemma for indexed derivative-closed families. -/
theorem ithom {Q : Finset ι} {ev : ι → ℝ[X]} (hQ : IDerivClosed Q ev) (μ : ι → SignType) :
    (iSign Q ev μ).OrdConnected ∧ ((iSign Q ev μ).Subsingleton ∨ IsOpen (iSign Q ev μ)) := by
  classical
  rcases (iSign Q ev μ).eq_empty_or_nonempty with he | ⟨x₀, h₀⟩
  · rw [he]; exact ⟨ordConnected_empty, Or.inl subsingleton_empty⟩
  · rw [iSign_eq_signSet h₀]
    exact thom _ _ le_rfl (derivClosed_image hQ) _

theorem ithom_relax {Q : Finset ι} {ev : ι → ℝ[X]} (hQ : IDerivClosed Q ev) {μ : ι → SignType}
    (hne : (iSign Q ev μ).Nonempty) : (iRelax Q ev μ).OrdConnected := by
  classical
  obtain ⟨x₀, h₀⟩ := hne
  rw [iRelax_eq_relaxSet h₀]
  exact thom_relax _ _ le_rfl (derivClosed_image hQ) _

/-- `iSign` contains a neighbourhood of `+∞` iff every code is the sign at `+∞`. -/
theorem eventually_mem_iSign_atTop_iff (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) :
    (∀ᶠ x in atTop, x ∈ iSign Q ev μ) ↔ ∀ i ∈ Q, μ i = SignType.sign (ev i).leadingCoeff := by
  have hall : ∀ᶠ x in atTop, ∀ i ∈ Q, SignType.sign ((ev i).eval x) =
      SignType.sign (ev i).leadingCoeff :=
    (Filter.eventually_all_finset Q).mpr fun i _ => eventually_sign_atTop (ev i)
  constructor
  · intro h
    obtain ⟨x, hx1, hx2⟩ := (h.and hall).exists
    intro i hi
    exact (hx1 i hi).symm.trans (hx2 i hi)
  · intro h
    filter_upwards [hall] with x hx
    exact fun i hi => (hx i hi).trans (h i hi).symm

theorem eventually_mem_iSign_atBot_iff (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) :
    (∀ᶠ x in atBot, x ∈ iSign Q ev μ) ↔
      ∀ i ∈ Q, μ i = SignType.sign ((ev i).comp (-X)).leadingCoeff := by
  have hall : ∀ᶠ x in atBot, ∀ i ∈ Q, SignType.sign ((ev i).eval x) =
      SignType.sign ((ev i).comp (-X)).leadingCoeff :=
    (Filter.eventually_all_finset Q).mpr fun i _ => eventually_sign_atBot (ev i)
  constructor
  · intro h
    obtain ⟨x, hx1, hx2⟩ := (h.and hall).exists
    intro i hi
    exact (hx1 i hi).symm.trans (hx2 i hi)
  · intro h
    filter_upwards [hall] with x hx
    exact fun i hi => (hx i hi).trans (h i hi).symm

theorem isClosed_relax (q : ℝ[X]) (s : SignType) :
    IsClosed {x : ℝ | Relax s (SignType.sign (q.eval x))} := by
  have hc : Continuous fun x : ℝ => q.eval x := q.continuous
  rcases s with _ | _ | _
  · have : {x : ℝ | Relax SignType.zero (SignType.sign (q.eval x))} = {x | q.eval x = 0} := by
      ext x; simp only [mem_setOf_eq]
      rw [show SignType.zero = 0 from rfl, relax_iff]
      constructor
      · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · exact h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
      · intro h; exact Or.inl ⟨rfl, h⟩
    rw [this]; exact isClosed_eq hc continuous_const
  · have : {x : ℝ | Relax SignType.neg (SignType.sign (q.eval x))} = {x | q.eval x ≤ 0} := by
      ext x; simp only [mem_setOf_eq]
      rw [show SignType.neg = -1 from rfl, relax_iff]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact h
      · intro h; exact Or.inr (Or.inr ⟨rfl, h⟩)
    rw [this]; exact isClosed_le hc continuous_const
  · have : {x : ℝ | Relax SignType.pos (SignType.sign (q.eval x))} = {x | 0 ≤ q.eval x} := by
      ext x; simp only [mem_setOf_eq]
      rw [show SignType.pos = 1 from rfl, relax_iff]
      constructor
      · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩)
        · exact absurd h (by decide)
        · exact h
        · exact absurd h (by decide)
      · intro h; exact Or.inr (Or.inl ⟨rfl, h⟩)
    rw [this]; exact isClosed_le continuous_const hc

theorem closure_iSign_subset (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) :
    closure (iSign Q ev μ) ⊆ iRelax Q ev μ := by
  intro z hz
  show ∀ i ∈ Q, Relax (μ i) (SignType.sign ((ev i).eval z))
  intro i hi
  have hsub : iSign Q ev μ ⊆ {x | Relax (μ i) (SignType.sign ((ev i).eval x))} :=
    fun x hx => Or.inl (hx i hi)
  exact ((isClosed_relax (ev i) (μ i)).closure_subset_iff.mpr hsub) hz

/-- An infinite piece of the open segment from `z` towards `c`, within `ε` of `z`. -/
theorem exists_near_segment {c z ε : ℝ} (hcz : c ≠ z) (hε : 0 < ε) :
    ∃ I : Set ℝ, I.Infinite ∧ I ⊆ uIcc c z ∧ ∀ y ∈ I, dist y z < ε := by
  rcases lt_or_gt_of_ne hcz with h | h
  · refine ⟨Ioo (max c (z - ε)) z, Set.Ioo_infinite (max_lt h (by linarith)), ?_, ?_⟩
    · intro y hy
      rw [mem_uIcc]; left
      exact ⟨(le_max_left _ _).trans hy.1.le, hy.2.le⟩
    · intro y hy
      have h1 := (le_max_right c (z - ε)).trans_lt hy.1
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.2]
  · refine ⟨Ioo z (min c (z + ε)), Set.Ioo_infinite (lt_min h (by linarith)), ?_, ?_⟩
    · intro y hy
      rw [mem_uIcc]; right
      exact ⟨hy.1.le, hy.2.le.trans (min_le_left _ _)⟩
    · intro y hy
      have h1 := hy.2.trans_le (min_le_right c (z + ε))
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1]

/-- A point of the relaxed set of a nonempty cell lies in the closure of the cell
(given the relaxed set is order-connected, e.g. by `ithom_relax`). -/
theorem mem_closure_of_iRelax {Q : Finset ι} {ev : ι → ℝ[X]} {μ : ι → SignType}
    (hR : (iRelax Q ev μ).OrdConnected) {c z : ℝ} (hc : c ∈ iSign Q ev μ)
    (hz : z ∈ iRelax Q ev μ) : z ∈ closure (iSign Q ev μ) := by
  classical
  rcases eq_or_ne c z with hcz | hcz
  · subst hcz; exact subset_closure hc
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨I, hIinf, hIsub, hIdist⟩ := exists_near_segment hcz hε
  set B : Finset ι := Q.filter (fun i => μ i ≠ 0)
  have hBne : ∀ i ∈ B, ev i ≠ 0 := by
    intro i hi h0
    obtain ⟨hiQ, hμ⟩ := Finset.mem_filter.mp hi
    have := hc i hiQ
    rw [h0, eval_zero, sign_zero] at this
    exact hμ this.symm
  have hfin : (⋃ i ∈ B, {x : ℝ | (ev i).IsRoot x}).Finite :=
    (B.finite_toSet).biUnion fun i hi => Polynomial.finite_setOfPred_isRoot (hBne i hi)
  obtain ⟨y, hyI, hyB⟩ := (hIinf.sdiff hfin).nonempty
  refine ⟨y, ?_, by rw [dist_comm]; exact hIdist y hyI⟩
  have hyR : y ∈ iRelax Q ev μ :=
    hR.uIcc_subset (iSign_subset_iRelax Q ev μ hc) hz (hIsub hyI)
  intro i hi
  rcases hyR i hi with h | h
  · exact h
  · by_cases hμ : μ i = 0
    · rw [h, hμ]
    · exfalso
      apply hyB
      refine mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hμ⟩, ?_⟩
      show (ev i).eval y = 0
      exact sign_eq_zero_iff.mp h

end Indexed

section Realized

variable {C : Set ℝ} {f : ℝ → ℝ}

/-- Positive values of a strictly monotone continuous function on an open interval `C` are
realized iff it is positive at a finite endpoint or eventually positive at an infinite end. -/
theorem realized_pos_iff (hC : C.OrdConnected) (hCo : IsOpen C)
    (hm : StrictMonoOn f C ∨ StrictAntiOn f C) (hf : Continuous f) :
    (∃ y ∈ C, 0 < f y) ↔ (∃ z ∈ closure C, z ∉ C ∧ 0 < f z) ∨
      ((∀ᶠ x in atTop, x ∈ C) ∧ ∀ᶠ x in atTop, 0 < f x) ∨
      ((∀ᶠ x in atBot, x ∈ C) ∧ ∀ᶠ x in atBot, 0 < f x) := by
  constructor
  · rintro ⟨y, hy, hfy⟩
    rcases hm with hm | hm
    · by_cases htop : ∀ᶠ x in atTop, x ∈ C
      · right; left
        refine ⟨htop, ?_⟩
        filter_upwards [htop, eventually_ge_atTop y] with x hx hxy
        exact lt_of_lt_of_le hfy (hm.monotoneOn hy hx hxy)
      · left
        have hb : ∃ b, y ≤ b ∧ b ∉ C := by
          by_contra hcon
          push Not at hcon
          exact htop (eventually_atTop.mpr ⟨y, hcon⟩)
        obtain ⟨b, hyb, hbC⟩ := hb
        set S := C ∩ Ici y with hS
        have hSb : BddAbove S := by
          refine ⟨b, fun c hc => ?_⟩
          by_contra hbc
          push Not at hbc
          exact hbC (hC.out hy hc.1 ⟨hyb, hbc.le⟩)
        have hSne : S.Nonempty := ⟨y, hy, le_refl y⟩
        have hyβ : y ≤ sSup S := le_csSup hSb ⟨hy, le_refl y⟩
        have hβcl : sSup S ∈ closure S := csSup_mem_closure hSne hSb
        refine ⟨sSup S, closure_mono inter_subset_left hβcl, ?_, ?_⟩
        · intro hβ
          obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hCo _ hβ
          have hmem : sSup S + ε / 2 ∈ C :=
            hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
          have := le_csSup hSb ⟨hmem, by show y ≤ _; linarith⟩
          linarith
        · have hT : IsClosed {x | f y ≤ f x} := isClosed_le continuous_const hf
          have hST : S ⊆ {x | f y ≤ f x} := fun c hc => hm.monotoneOn hy hc.1 hc.2
          have := (hT.closure_subset_iff.mpr hST) hβcl
          exact lt_of_lt_of_le hfy this
    · by_cases hbot : ∀ᶠ x in atBot, x ∈ C
      · right; right
        refine ⟨hbot, ?_⟩
        filter_upwards [hbot, eventually_le_atBot y] with x hx hxy
        exact lt_of_lt_of_le hfy (hm.antitoneOn hx hy hxy)
      · left
        have hb : ∃ b, b ≤ y ∧ b ∉ C := by
          by_contra hcon
          push Not at hcon
          exact hbot (eventually_atBot.mpr ⟨y, hcon⟩)
        obtain ⟨b, hyb, hbC⟩ := hb
        set S := C ∩ Iic y with hS
        have hSb : BddBelow S := by
          refine ⟨b, fun c hc => ?_⟩
          by_contra hbc
          push Not at hbc
          exact hbC (hC.out hc.1 hy ⟨hbc.le, hyb⟩)
        have hSne : S.Nonempty := ⟨y, hy, le_refl y⟩
        have hyβ : sInf S ≤ y := csInf_le hSb ⟨hy, le_refl y⟩
        have hβcl : sInf S ∈ closure S := csInf_mem_closure hSne hSb
        refine ⟨sInf S, closure_mono inter_subset_left hβcl, ?_, ?_⟩
        · intro hβ
          obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hCo _ hβ
          have hmem : sInf S - ε / 2 ∈ C :=
            hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
          have := csInf_le hSb ⟨hmem, by show _ ≤ y; linarith⟩
          linarith
        · have hT : IsClosed {x | f y ≤ f x} := isClosed_le continuous_const hf
          have hST : S ⊆ {x | f y ≤ f x} := fun c hc => hm.antitoneOn hc.1 hy hc.2
          have := (hT.closure_subset_iff.mpr hST) hβcl
          exact lt_of_lt_of_le hfy this
  · rintro (⟨z, hzc, -, hz⟩ | ⟨htop, hpos⟩ | ⟨hbot, hpos⟩)
    · have hU : {x | 0 < f x} ∈ 𝓝 z := (isOpen_lt continuous_const hf).mem_nhds hz
      obtain ⟨y, hyU, hyC⟩ := mem_closure_iff_nhds.mp hzc _ hU
      exact ⟨y, hyC, hyU⟩
    · obtain ⟨x, h1, h2⟩ := (htop.and hpos).exists
      exact ⟨x, h1, h2⟩
    · obtain ⟨x, h1, h2⟩ := (hbot.and hpos).exists
      exact ⟨x, h1, h2⟩

/-- Negative version of `realized_pos_iff`. -/
theorem realized_neg_iff (hC : C.OrdConnected) (hCo : IsOpen C)
    (hm : StrictMonoOn f C ∨ StrictAntiOn f C) (hf : Continuous f) :
    (∃ y ∈ C, f y < 0) ↔ (∃ z ∈ closure C, z ∉ C ∧ f z < 0) ∨
      ((∀ᶠ x in atTop, x ∈ C) ∧ ∀ᶠ x in atTop, f x < 0) ∨
      ((∀ᶠ x in atBot, x ∈ C) ∧ ∀ᶠ x in atBot, f x < 0) := by
  have hm' : StrictMonoOn (fun x => -f x) C ∨ StrictAntiOn (fun x => -f x) C := by
    rcases hm with hm | hm
    · exact Or.inr fun a ha b hb hab => neg_lt_neg (hm ha hb hab)
    · exact Or.inl fun a ha b hb hab => neg_lt_neg (hm ha hb hab)
  have := realized_pos_iff hC hCo hm' hf.neg
  simp only [neg_pos] at this
  exact this

/-- A zero is realized iff both strict signs are realized. -/
theorem realized_zero_iff (hC : C.OrdConnected) (hCo : IsOpen C)
    (hm : StrictMonoOn f C ∨ StrictAntiOn f C) (hf : Continuous f) :
    (∃ y ∈ C, f y = 0) ↔ (∃ y ∈ C, 0 < f y) ∧ (∃ y ∈ C, f y < 0) := by
  constructor
  · rintro ⟨y, hy, h0⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hCo y hy
    have hl : y - ε / 2 ∈ C :=
      hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    have hr : y + ε / 2 ∈ C :=
      hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    rcases hm with hm | hm
    · have h1 := hm hl hy (by linarith)
      have h2 := hm hy hr (by linarith)
      exact ⟨⟨_, hr, by linarith⟩, ⟨_, hl, by linarith⟩⟩
    · have h1 := hm hl hy (by linarith)
      have h2 := hm hy hr (by linarith)
      exact ⟨⟨_, hl, by linarith⟩, ⟨_, hr, by linarith⟩⟩
  · rintro ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩
    have hsub : uIcc a b ⊆ C := hC.uIcc_subset ha hb
    obtain ⟨x, hx, hfx⟩ := intermediate_value_uIcc (hf.continuousOn : ContinuousOn f (uIcc a b))
      (show (0 : ℝ) ∈ uIcc (f a) (f b) from mem_uIcc.mpr (Or.inr ⟨hfb.le, hfa.le⟩))
    exact ⟨x, hsub hx, hfx⟩

end Realized

end SubanalyticLib

/-! SubanalyticLib CS-3 (Tarski–Seidenberg) infrastructure, part 1.
* `IsSA R S`: `S ⊆ A` lies in the Boolean algebra generated by `{f > 0}`, `{f = 0}` for `f` in a
  subring `R` of `A → ℝ` (polynomial functions give semialgebraic sets, analytic germs on a ball
  give semianalytic sets). Closure lemmas and finite-cover locality.
* Pseudo-division in `S[X]` over any commutative ring (with an even power of the leading
  coefficient, so that signs at the roots of the divisor are preserved). -/

open Polynomial Set

set_option linter.unusedSectionVars false

namespace SubanalyticLib

section SA

variable {A : Type*} (R : Subring (A → ℝ))

/-- Boolean algebra generated by the sign conditions of the functions in `R`. -/
inductive IsSA : Set A → Prop
  | pos {f : A → ℝ} (hf : f ∈ R) : IsSA {a | 0 < f a}
  | zero {f : A → ℝ} (hf : f ∈ R) : IsSA {a | f a = 0}
  | compl {S : Set A} : IsSA S → IsSA Sᶜ
  | inter {S T : Set A} : IsSA S → IsSA T → IsSA (S ∩ T)

variable {R}

theorem IsSA.univ : IsSA R (Set.univ : Set A) := by
  have h := IsSA.zero (R := R) (Subring.zero_mem R)
  have : {a : A | (0 : A → ℝ) a = 0} = Set.univ := by ext a; simp
  rwa [this] at h

theorem IsSA.empty : IsSA R (∅ : Set A) := by
  have h := (IsSA.univ (R := R)).compl
  rwa [Set.compl_univ] at h

theorem IsSA.union {S T : Set A} (hS : IsSA R S) (hT : IsSA R T) : IsSA R (S ∪ T) := by
  have h := (hS.compl.inter hT.compl).compl
  rwa [← Set.compl_union, compl_compl] at h

theorem IsSA.neg {f : A → ℝ} (hf : f ∈ R) : IsSA R {a | f a < 0} := by
  have h := IsSA.pos (R := R) (Subring.neg_mem R hf)
  have : {a : A | 0 < (-f) a} = {a | f a < 0} := by ext a; simp
  rwa [this] at h

theorem IsSA.ne {f : A → ℝ} (hf : f ∈ R) : IsSA R {a | f a ≠ 0} := by
  have h := (IsSA.zero (R := R) hf).compl
  exact h

theorem IsSA.sign {f : A → ℝ} (hf : f ∈ R) (s : SignType) :
    IsSA R {a | SignType.sign (f a) = s} := by
  rcases s with _ | _ | _
  · have : {a : A | SignType.sign (f a) = SignType.zero} = {a | f a = 0} := by
      ext a; simp only [mem_setOf_eq]; exact sign_eq_zero_iff
    rw [this]; exact IsSA.zero hf
  · have : {a : A | SignType.sign (f a) = SignType.neg} = {a | f a < 0} := by
      ext a; simp only [mem_setOf_eq]; exact sign_eq_neg_one_iff
    rw [this]; exact IsSA.neg hf
  · have : {a : A | SignType.sign (f a) = SignType.pos} = {a | 0 < f a} := by
      ext a; simp only [mem_setOf_eq]; exact sign_eq_one_iff
    rw [this]; exact IsSA.pos hf

theorem IsSA.biUnion {ι : Type*} (s : Finset ι) {S : ι → Set A} (h : ∀ i ∈ s, IsSA R (S i)) :
    IsSA R (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]; exact IsSA.empty
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (h i (Finset.mem_insert_self i s)).union
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem IsSA.biInter {ι : Type*} (s : Finset ι) {S : ι → Set A} (h : ∀ i ∈ s, IsSA R (S i)) :
    IsSA R (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, iInter_of_empty, iInter_univ]; exact IsSA.univ
  | insert i s hi ih =>
    rw [Finset.set_biInter_insert]
    exact (h i (Finset.mem_insert_self i s)).inter
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem IsSA.iUnion_fintype {ι : Type*} [Fintype ι] {S : ι → Set A} (h : ∀ i, IsSA R (S i)) :
    IsSA R (⋃ i, S i) := by
  have := IsSA.biUnion (R := R) Finset.univ (S := S) (fun i _ => h i)
  simpa using this

theorem IsSA.iInter_fintype {ι : Type*} [Fintype ι] {S : ι → Set A} (h : ∀ i, IsSA R (S i)) :
    IsSA R (⋂ i, S i) := by
  have := IsSA.biInter (R := R) Finset.univ (S := S) (fun i _ => h i)
  simpa using this

/-- Locality: `E` is SA if it is SA on each piece of a finite SA cover. -/
theorem IsSA.of_cover {ι : Type*} [Fintype ι] {C : ι → Set A} (hC : ∀ i, IsSA R (C i))
    (hcov : ∀ a, ∃ i, a ∈ C i) {E : Set A} (hE : ∀ i, IsSA R (E ∩ C i)) : IsSA R E := by
  have : E = ⋃ i, E ∩ C i := by
    ext a; constructor
    · intro ha; obtain ⟨i, hi⟩ := hcov a; exact mem_iUnion.mpr ⟨i, ha, hi⟩
    · intro ha; obtain ⟨i, hi⟩ := mem_iUnion.mp ha; exact hi.1
  rw [this]; exact IsSA.iUnion_fintype hE

/-- Evaluation of the coefficient functions at a parameter `a`. -/
def evR (a : A) : R →+* ℝ := (Pi.evalRingHom (fun _ : A => ℝ) a).comp R.subtype

theorem evR_apply (a : A) (f : R) : evR (R := R) a f = (f : A → ℝ) a := rfl

/-- A polynomial with coefficients in `R`, specialised at the parameter `a`. -/
noncomputable def pe (p : R[X]) (a : A) : ℝ[X] := p.map (evR (R := R) a)

/-- The function `a ↦ (p at a)(x₀)`-style coefficient functions lie in `R`. -/
theorem coeff_mem (p : R[X]) (i : ℕ) : ((p.coeff i : R) : A → ℝ) ∈ R := (p.coeff i).2

theorem pe_coeff (p : R[X]) (a : A) (i : ℕ) : (pe p a).coeff i = ((p.coeff i : R) : A → ℝ) a := by
  simp [pe, coeff_map, evR_apply]

end SA

section PseudoDiv

variable {S : Type*} [CommRing S]

/-- One elimination step of pseudo-division. -/
theorem pdiv_step (p q : S[X]) (hq : q.natDegree ≤ p.natDegree) (hp : 0 < p.natDegree) :
    (q.leadingCoeff • p - C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q).natDegree <
      p.natDegree := by
  set p1 := q.leadingCoeff • p - C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q with hp1
  have hc : ∀ i, p.natDegree ≤ i → p1.coeff i = 0 := by
    intro i hi
    rw [hp1, coeff_sub, coeff_smul, mul_assoc, coeff_C_mul, coeff_X_pow_mul', smul_eq_mul]
    rw [if_pos (le_trans (Nat.sub_le _ _) hi)]
    rcases eq_or_lt_of_le hi with h | h
    · subst h
      have : p.natDegree - (p.natDegree - q.natDegree) = q.natDegree := by omega
      rw [this]
      rw [coeff_natDegree, coeff_natDegree]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt h]
      have : q.natDegree < i - (p.natDegree - q.natDegree) := by omega
      rw [coeff_eq_zero_of_natDegree_lt this]
      ring
  by_cases h0 : p1 = 0
  · rw [h0, natDegree_zero]; exact hp
  · rw [natDegree_lt_iff_degree_lt h0, degree_lt_iff_coeff_zero]
    intro m hm
    exact hc m (by exact_mod_cast hm)

/-- **Pseudo-division**: `lc(q)^k • p = s * q + r` with `deg r < deg q`. -/
theorem pseudo_div (q : S[X]) (hq : 0 < q.natDegree) (p : S[X]) :
    ∃ k : ℕ, ∃ s r : S[X], q.leadingCoeff ^ k • p = s * q + r ∧ r.natDegree < q.natDegree := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hlt : p.natDegree < q.natDegree
    · exact ⟨0, 0, p, by simp, hlt⟩
    · push Not at hlt
      have hp : 0 < p.natDegree := lt_of_lt_of_le hq hlt
      set m := p.natDegree - q.natDegree
      set p1 := q.leadingCoeff • p - C p.leadingCoeff * X ^ m * q with hp1
      have hdeg : p1.natDegree < n := hn ▸ pdiv_step p q hlt hp
      obtain ⟨k, s, r, hk, hr⟩ := ih p1.natDegree hdeg p1 rfl
      refine ⟨k + 1, s + C (q.leadingCoeff ^ k * p.leadingCoeff) * X ^ m, r, ?_, hr⟩
      have e1 : q.leadingCoeff • p = p1 + C p.leadingCoeff * X ^ m * q := by
        rw [hp1]; ring
      rw [pow_succ, mul_smul, e1, smul_add, hk]
      rw [smul_eq_C_mul]
      simp only [map_mul, map_pow]
      ring

/-- Pseudo-division with an even power of the leading coefficient. -/
theorem pseudo_div_even (q : S[X]) (hq : 0 < q.natDegree) (p : S[X]) :
    ∃ k : ℕ, ∃ s r : S[X], q.leadingCoeff ^ (2 * k) • p = s * q + r ∧
      r.natDegree < q.natDegree := by
  obtain ⟨k, s, r, h, hr⟩ := pseudo_div q hq p
  refine ⟨k, q.leadingCoeff ^ k • s, q.leadingCoeff ^ k • r, ?_, ?_⟩
  · rw [two_mul, pow_add, mul_smul, h, smul_add, smul_mul_assoc]
  · exact lt_of_le_of_lt (natDegree_smul_le _ _) hr

end PseudoDiv

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-b (part 1): per-parameter cell lemmas for the Cohen–Hörmander step.
* `sign_at_root`: at a root of `q`, `P` has the sign of its pseudo-remainder by `q`.
* realized signs of a strictly increasing continuous function on an open order-connected set
  `C`, read off from its eventual signs at the two ends of `C` (filters `atBot`/`atTop` of the
  subtype `C`). -/

open Polynomial Set Filter

set_option linter.unusedSectionVars false

namespace SubanalyticLib

/-- At a root of `q`, `P` has the sign of the pseudo-remainder. -/
theorem sign_at_root {P q s r : ℝ[X]} {c : ℝ} {k : ℕ} (hc : c ≠ 0)
    (h : c ^ (2 * k) • P = s * q + r) {x : ℝ} (hx : q.eval x = 0) :
    SignType.sign (P.eval x) = SignType.sign (r.eval x) := by
  have e := congrArg (fun F : ℝ[X] => F.eval x) h
  simp only [eval_smul, smul_eq_mul, eval_add, eval_mul, hx, mul_zero, zero_add] at e
  rw [← e, sign_mul]
  have : SignType.sign (c ^ (2 * k)) = 1 := by
    rw [sign_eq_one_iff, pow_mul]
    exact pow_pos (by positivity) k
  rw [this, one_mul]

section Realized

variable {C : Set ℝ} {f : ℝ → ℝ}

end Realized

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-c: parametric families, codes, the (max degree, count) measure and
normalisation by truncation (so that formal degree = effective degree on each branch).
Appended to L4TB.lean (= L4t_Thom + L4tc_Ends + L4s_SA + L4tb_Cells). -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSc

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

/-- Parameters at which the sign condition `ν` on the specialised family is realized. -/
def Rlz (F : Finset ι) (ev : ι → R[X]) (ν : ι → SignType) : Set A :=
  {a | (iSign F (fun i => pe (ev i) a) ν).Nonempty}

/-- Derivative-closed at every parameter of `B`. -/
def DCl (F : Finset ι) (ev : ι → R[X]) (B : Set A) : Prop :=
  ∀ a ∈ B, IDerivClosed F (fun i => pe (ev i) a)

/-- Formal degree = effective degree on `B` (or the polynomial is formally zero). -/
def Nrm (F : Finset ι) (ev : ι → R[X]) (B : Set A) : Prop :=
  ∀ i ∈ F, ∀ a ∈ B, (((ev i).leadingCoeff : R) : A → ℝ) a ≠ 0 ∨ ev i = 0

/-- Codes on `s`, extended by `0`. -/
noncomputable def codes (s : Finset ι) : Finset (ι → SignType) :=
  (Finset.univ : Finset (s → SignType)).image (fun c i => if h : i ∈ s then c ⟨i, h⟩ else 0)

theorem exists_code (s : Finset ι) (μ : ι → SignType) : ∃ c ∈ codes s, ∀ i ∈ s, c i = μ i :=
  ⟨_, Finset.mem_image.mpr ⟨fun i => μ i, Finset.mem_univ _, rfl⟩, fun i hi => by simp [hi]⟩

theorem Rlz_congr {F : Finset ι} {ev ev' : ι → R[X]} {ν ν' : ι → SignType} {a : A}
    (he : ∀ i ∈ F, pe (ev i) a = pe (ev' i) a) (hν : ∀ i ∈ F, ν i = ν' i) :
    a ∈ Rlz F ev ν ↔ a ∈ Rlz F ev' ν' := by
  simp only [Rlz, mem_setOf_eq, iSign]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, fun i hi => by rw [← he i hi, ← hν i hi]; exact hy i hi⟩
  · rintro ⟨y, hy⟩; exact ⟨y, fun i hi => by rw [he i hi, hν i hi]; exact hy i hi⟩

/-! ### The measure -/

/-- Maximal formal degree. -/
noncomputable def mdeg (F : Finset ι) (ev : ι → R[X]) : ℕ := F.sup fun i => (ev i).natDegree

/-- Number of members of maximal formal degree. -/
noncomputable def mcnt (F : Finset ι) (ev : ι → R[X]) : ℕ :=
  (F.filter fun i => (ev i).natDegree = mdeg F ev).card

noncomputable def mord (F : Finset ι) (ev : ι → R[X]) : ℕ ×ₗ ℕ := toLex (mdeg F ev, mcnt F ev)

theorem natDegree_le_mdeg {F : Finset ι} {ev : ι → R[X]} {i : ι} (hi : i ∈ F) :
    (ev i).natDegree ≤ mdeg F ev :=
  Finset.le_sup (f := fun i => (ev i).natDegree) hi

theorem mdeg_le {F : Finset ι} {ev : ι → R[X]} {n : ℕ} (h : ∀ i ∈ F, (ev i).natDegree ≤ n) :
    mdeg F ev ≤ n := Finset.sup_le h

theorem mord_mono {F : Finset ι} {ev ev' : ι → R[X]}
    (h : ∀ i ∈ F, (ev' i).natDegree ≤ (ev i).natDegree) : mord F ev' ≤ mord F ev := by
  have hle : mdeg F ev' ≤ mdeg F ev := mdeg_le fun i hi => (h i hi).trans (natDegree_le_mdeg hi)
  rw [mord, mord, Prod.Lex.toLex_le_toLex]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, le_antisymm (natDegree_le_mdeg hi.1) ?_⟩
    rw [← heq, ← hi.2]; exact h i hi.1

theorem mord_lt {ι' : Type*} {F : Finset ι} {ev : ι → R[X]} {F' : Finset ι'} {ev' : ι' → R[X]}
    (h1 : ∀ i ∈ F', (ev' i).natDegree ≤ mdeg F ev)
    (h2 : (F'.filter fun i => (ev' i).natDegree = mdeg F ev).card < mcnt F ev) :
    mord F' ev' < mord F ev := by
  have hle : mdeg F' ev' ≤ mdeg F ev := mdeg_le h1
  rw [mord, mord, Prod.Lex.toLex_lt_toLex]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    rw [mcnt, heq]; exact h2

/-! ### Truncation -/

/-- Keep the coefficients of index `< k`. -/
noncomputable def ptr (k : ℕ) (p : R[X]) : R[X] := ∑ j ∈ Finset.range k, monomial j (p.coeff j)

theorem coeff_ptr (k : ℕ) (p : R[X]) (n : ℕ) :
    (ptr k p).coeff n = if n < k then p.coeff n else 0 := by
  simp only [ptr, finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]

theorem natDegree_ptr_le (k : ℕ) (p : R[X]) : (ptr k p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_ptr]
  split_ifs
  · exact coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hn)
  · rfl

theorem ptr_zero (p : R[X]) : ptr 0 p = 0 := by simp [ptr]

theorem lc_ptr {m : ℕ} {p : R[X]} (h : p.coeff m ≠ 0) :
    (ptr (m + 1) p).natDegree = m ∧ (ptr (m + 1) p).leadingCoeff = p.coeff m := by
  have hc : (ptr (m + 1) p).coeff m = p.coeff m := by rw [coeff_ptr, if_pos (Nat.lt_succ_self m)]
  have hd : (ptr (m + 1) p).natDegree = m := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro n hn
      rw [coeff_ptr, if_neg]
      have : m < n := by exact_mod_cast hn
      omega
    · rw [hc]; exact h
  exact ⟨hd, by rw [leadingCoeff, hd, hc]⟩

theorem pe_ptr {k : ℕ} {p : R[X]} {a : A}
    (h : ∀ j, k ≤ j → ((p.coeff j : R) : A → ℝ) a = 0) : pe (ptr k p) a = pe p a := by
  ext n
  rw [pe_coeff, pe_coeff, coeff_ptr]
  split_ifs with hn
  · rfl
  · rw [h n (not_lt.mp hn)]; rfl

/-! ### Branches by effective degree -/

/-- Branch where exactly the coefficients of index `< k` may be nonzero and (if `k > 0`)
coefficient `k - 1` is nonzero; `D` bounds the formal degree. -/
def Br (D : ℕ) (p : R[X]) (k : ℕ) : Set A :=
  {a | (∀ j ∈ Finset.range (D + 1), k ≤ j → ((p.coeff j : R) : A → ℝ) a = 0) ∧
    (k = 0 ∨ ((p.coeff (k - 1) : R) : A → ℝ) a ≠ 0)}

theorem isSA_Br (D : ℕ) (p : R[X]) (k : ℕ) : IsSA R (Br (A := A) D p k) := by
  have h1 : IsSA R {a : A | ∀ j ∈ Finset.range (D + 1), k ≤ j → ((p.coeff j : R) : A → ℝ) a = 0} := by
    have : {a : A | ∀ j ∈ Finset.range (D + 1), k ≤ j → ((p.coeff j : R) : A → ℝ) a = 0} =
        ⋂ j ∈ (Finset.range (D + 1)).filter (fun j => k ≤ j), {a | ((p.coeff j : R) : A → ℝ) a = 0} := by
      ext a; simp only [mem_setOf_eq, mem_iInter, Finset.mem_filter, and_imp]
    rw [this]
    exact IsSA.biInter _ fun j _ => IsSA.zero (coeff_mem p j)
  have h2 : IsSA R {a : A | k = 0 ∨ ((p.coeff (k - 1) : R) : A → ℝ) a ≠ 0} := by
    by_cases hk : k = 0
    · have : {a : A | k = 0 ∨ ((p.coeff (k - 1) : R) : A → ℝ) a ≠ 0} = univ := by
        ext a; simp [hk]
      rw [this]; exact IsSA.univ
    · have : {a : A | k = 0 ∨ ((p.coeff (k - 1) : R) : A → ℝ) a ≠ 0} =
          {a | ((p.coeff (k - 1) : R) : A → ℝ) a ≠ 0} := by
        ext a; simp [hk]
      rw [this]; exact IsSA.ne (coeff_mem p _)
  exact h1.inter h2

/-- The effective number of coefficients at `a`. -/
noncomputable def effk (D : ℕ) (p : R[X]) (a : A) : ℕ :=
  ((Finset.range (D + 1)).filter fun j => ((p.coeff j : R) : A → ℝ) a ≠ 0).sup (· + 1)

theorem effk_le (D : ℕ) (p : R[X]) (a : A) : effk D p a ≤ D + 1 := by
  apply Finset.sup_le
  intro j hj
  have := (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  omega

theorem mem_Br_effk {D : ℕ} {p : R[X]} (hD : p.natDegree ≤ D) (a : A) :
    a ∈ Br D p (effk D p a) := by
  refine ⟨fun j hj hkj => ?_, ?_⟩
  · by_contra hne
    have : j + 1 ≤ effk D p a :=
      Finset.le_sup (f := (· + 1)) (Finset.mem_filter.mpr ⟨hj, hne⟩)
    omega
  · rcases Nat.eq_zero_or_pos (effk D p a) with h0 | hpos
    · exact Or.inl h0
    · right
      have hne : ((Finset.range (D + 1)).filter fun j => ((p.coeff j : R) : A → ℝ) a ≠ 0).Nonempty := by
        by_contra hem
        rw [Finset.not_nonempty_iff_eq_empty] at hem
        have : effk D p a = 0 := by rw [effk, hem]; rfl
        omega
      obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup _ hne (· + 1)
      have : effk D p a - 1 = j := by rw [effk, hjeq]; omega
      rw [this]
      exact (Finset.mem_filter.mp hj).2

/-- On `Br D p k` all coefficients of index `≥ k` vanish (`D ≥ natDegree p`). -/
theorem coeff_vanish_of_Br {D : ℕ} {p : R[X]} (hD : p.natDegree ≤ D) {k : ℕ} {a : A}
    (ha : a ∈ Br D p k) (j : ℕ) (hj : k ≤ j) : ((p.coeff j : R) : A → ℝ) a = 0 := by
  by_cases hjD : j ≤ D
  · exact ha.1 j (Finset.mem_range.mpr (Nat.lt_succ_of_le hjD)) hj
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; rfl

/-- Truncated family on the branch `e`. -/
noncomputable def evTr (F : Finset ι) (ev : ι → R[X]) (D : ℕ) (e : F → Fin (D + 2)) (i : ι) : R[X] :=
  if h : i ∈ F then ptr (e ⟨i, h⟩) (ev i) else ev i

/-- The branch `e`. -/
def BrE (F : Finset ι) (ev : ι → R[X]) (D : ℕ) (e : F → Fin (D + 2)) : Set A :=
  ⋂ i : F, Br D (ev i) (e i)

theorem isSA_BrE (F : Finset ι) (ev : ι → R[X]) (D : ℕ) (e : F → Fin (D + 2)) :
    IsSA R (BrE (A := A) F ev D e) :=
  IsSA.iInter_fintype fun i => isSA_Br D (ev i) (e i)

theorem pe_evTr {F : Finset ι} {ev : ι → R[X]} {D : ℕ} (hD : ∀ i ∈ F, (ev i).natDegree ≤ D)
    {e : F → Fin (D + 2)} {a : A} (ha : a ∈ BrE F ev D e) {i : ι} (hi : i ∈ F) :
    pe (evTr F ev D e i) a = pe (ev i) a := by
  rw [evTr, dif_pos hi]
  exact pe_ptr fun j hj => coeff_vanish_of_Br (hD i hi) (mem_iInter.mp ha ⟨i, hi⟩) j hj

theorem nrm_evTr {F : Finset ι} {ev : ι → R[X]} {D : ℕ} (e : F → Fin (D + 2)) :
    Nrm F (evTr F ev D e) (BrE F ev D e) := by
  intro i hi a ha
  have hb := mem_iInter.mp ha ⟨i, hi⟩
  rw [evTr, dif_pos hi]
  rcases Nat.eq_zero_or_pos (e ⟨i, hi⟩ : ℕ) with h0 | hpos
  · right; rw [h0]; exact ptr_zero _
  · left
    obtain ⟨m, hm⟩ : ∃ m, (e ⟨i, hi⟩ : ℕ) = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hcm : (((ev i).coeff m : R) : A → ℝ) a ≠ 0 := by
      rcases hb.2 with h | h
      · omega
      · rw [hm] at h; simpa using h
    have hc : (ev i).coeff m ≠ 0 := by
      intro h0; apply hcm; rw [h0]; rfl
    rw [hm, (lc_ptr hc).2]
    exact hcm

theorem natDegree_evTr_le {F : Finset ι} {ev : ι → R[X]} {D : ℕ} (e : F → Fin (D + 2)) (i : ι) :
    (evTr F ev D e i).natDegree ≤ (ev i).natDegree := by
  rw [evTr]; split_ifs
  · exact natDegree_ptr_le _ _
  · exact le_rfl

theorem dcl_evTr {F : Finset ι} {ev : ι → R[X]} {D : ℕ} (hD : ∀ i ∈ F, (ev i).natDegree ≤ D)
    {B : Set A} (hB : DCl F ev B) (e : F → Fin (D + 2)) :
    DCl F (evTr F ev D e) (B ∩ BrE F ev D e) := by
  intro a ha i hi
  obtain ⟨j, hj, hje⟩ := hB a ha.1 i hi
  refine ⟨j, hj, ?_⟩
  show pe (evTr F ev D e j) a = derivative (pe (evTr F ev D e i) a)
  rw [pe_evTr hD ha.2 hj, pe_evTr hD ha.2 hi]
  exact hje

/-- **Normalisation**: to show `B ∩ Rlz F ev ν` is SA it suffices to treat every truncated,
normalised family on its branch. -/
theorem isSA_of_branches {F : Finset ι} {ev : ι → R[X]} {ν : ι → SignType} {B : Set A}
    (hBsa : IsSA R B) (D : ℕ) (hD : ∀ i ∈ F, (ev i).natDegree ≤ D)
    (h : ∀ e : F → Fin (D + 2),
      IsSA R ((B ∩ BrE F ev D e) ∩ Rlz F (evTr F ev D e) ν)) :
    IsSA R (B ∩ Rlz F ev ν) := by
  refine IsSA.of_cover (C := fun e : F → Fin (D + 2) => BrE F ev D e) (isSA_BrE F ev D) ?_ ?_
  · intro a
    refine ⟨fun i => ⟨effk D (ev i) a, Nat.lt_succ_of_le (effk_le D (ev i) a)⟩, ?_⟩
    exact mem_iInter.mpr fun i => mem_Br_effk (hD i i.2) a
  · intro e
    have : (B ∩ Rlz F ev ν) ∩ BrE F ev D e = (B ∩ BrE F ev D e) ∩ Rlz F (evTr F ev D e) ν := by
      ext a
      simp only [mem_inter_iff]
      constructor
      · rintro ⟨⟨hB, hR⟩, hE⟩
        exact ⟨⟨hB, hE⟩, (Rlz_congr (fun i hi => (pe_evTr hD hE hi).symm) fun _ _ => rfl).mp hR⟩
      · rintro ⟨⟨hB, hE⟩, hR⟩
        exact ⟨⟨hB, (Rlz_congr (fun i hi => (pe_evTr hD hE hi)) fun _ _ => rfl).mp hR⟩, hE⟩
    rw [this]
    exact h e

end TSc

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-d (part 1): data of one Cohen–Hörmander elimination step.
A normalised derivative-closed family `F`, a member `iP` of maximal degree `d ≥ 1`,
`Q = F.erase iP`, pseudo-remainders `rem q` of `P` by each nonconstant `q ∈ Q`, and the new
family `F' = Q ⊕ {derivatives of the remainders}` (index type `ι ⊕ (ι × ℕ)`), which has
smaller (max degree, count) measure. Appended to L4TD.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSd

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

theorem pe_nrm {p : R[X]} {a : A} (h : ((p.leadingCoeff : R) : A → ℝ) a ≠ 0 ∨ p = 0) :
    (pe p a).natDegree = p.natDegree ∧
      (pe p a).leadingCoeff = ((p.leadingCoeff : R) : A → ℝ) a := by
  rcases h with h | h
  · have h' : evR (R := R) a p.leadingCoeff ≠ 0 := h
    exact ⟨natDegree_map_of_leadingCoeff_ne_zero _ h', leadingCoeff_map_of_leadingCoeff_ne_zero _ h'⟩
  · subst h
    rw [pe, Polynomial.map_zero, natDegree_zero, leadingCoeff_zero, leadingCoeff_zero]
    exact ⟨rfl, rfl⟩

theorem pe_iterate_derivative (p : R[X]) (a : A) (k : ℕ) :
    pe (derivative^[k] p) a = derivative^[k] (pe p a) :=
  (iterate_derivative_map p (evR a) k).symm

theorem pe_identity {P q s r : R[X]} {k : ℕ} (h : q.leadingCoeff ^ (2 * k) • P = s * q + r)
    (a : A) : (((q.leadingCoeff : R) : A → ℝ) a) ^ (2 * k) • pe P a = pe s a * pe q a + pe r a := by
  have := congrArg (Polynomial.map (evR (R := R) a)) h
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.smul_eq_C_mul, Polynomial.map_mul,
    Polynomial.map_C] at this
  rw [Polynomial.smul_eq_C_mul]
  simpa [pe, map_pow, evR_apply] using this

theorem pe_zero' (a : A) : pe (0 : R[X]) a = 0 := by simp [pe]

/-- Data of one elimination step on the branch `B`. -/
structure SD (F : Finset ι) (ev : ι → R[X]) (B : Set A) where
  iP : ι
  hiP : iP ∈ F
  hdeg : (ev iP).natDegree = mdeg F ev
  hpos : 0 < mdeg F ev
  rem : ι → R[X]
  kk : ι → ℕ
  ss : ι → R[X]
  hrem : ∀ i, 0 < (ev i).natDegree →
    (ev i).leadingCoeff ^ (2 * kk i) • ev iP = ss i * ev i + rem i ∧
      (rem i).natDegree < (ev i).natDegree
  hN : Nrm F ev B
  hD : DCl F ev B

theorem exists_rem (ev : ι → R[X]) (P : R[X]) :
    ∃ kk : ι → ℕ, ∃ ss rem : ι → R[X], ∀ i, 0 < (ev i).natDegree →
      (ev i).leadingCoeff ^ (2 * kk i) • P = ss i * ev i + rem i ∧
        (rem i).natDegree < (ev i).natDegree := by
  have : ∀ i, ∃ k : ℕ, ∃ s r : R[X], 0 < (ev i).natDegree →
      (ev i).leadingCoeff ^ (2 * k) • P = s * ev i + r ∧ r.natDegree < (ev i).natDegree := by
    intro i
    by_cases h : 0 < (ev i).natDegree
    · obtain ⟨k, s, r, h1, h2⟩ := pseudo_div_even (ev i) h P
      exact ⟨k, s, r, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, 0, 0, fun h' => absurd h' h⟩
  choose kk ss rem h using this
  exact ⟨kk, ss, rem, h⟩

/-- New index set. -/
noncomputable def Fp (Q : Finset ι) (ev : ι → R[X]) (d : ℕ) : Finset (ι ⊕ (ι × ℕ)) :=
  Q.disjSum ((Q.filter fun i => 0 < (ev i).natDegree) ×ˢ Finset.range (d + 1))

/-- New family. -/
noncomputable def evp (ev rem : ι → R[X]) : ι ⊕ (ι × ℕ) → R[X] :=
  Sum.elim ev (fun x => derivative^[x.2] (rem x.1))

theorem mem_Fp_inl {Q : Finset ι} {ev : ι → R[X]} {d : ℕ} {i : ι} :
    Sum.inl i ∈ Fp Q ev d ↔ i ∈ Q := by simp [Fp]

theorem mem_Fp_inr {Q : Finset ι} {ev : ι → R[X]} {d : ℕ} {i : ι} {j : ℕ} :
    Sum.inr (i, j) ∈ Fp Q ev d ↔ (i ∈ Q ∧ 0 < (ev i).natDegree) ∧ j < d + 1 := by
  simp [Fp]

variable {F : Finset ι} {ev : ι → R[X]} {B : Set A}

namespace SD

variable (S : SD F ev B)

/-- The rest of the family. -/
noncomputable def Q : Finset ι := F.erase S.iP

/-- The new family's index set. -/
noncomputable def F' : Finset (ι ⊕ (ι × ℕ)) := Fp S.Q ev (mdeg F ev)

/-- The new family. -/
noncomputable def ev' : ι ⊕ (ι × ℕ) → R[X] := evp ev S.rem

theorem mem_Q {i : ι} : i ∈ S.Q ↔ i ≠ S.iP ∧ i ∈ F := Finset.mem_erase

theorem mem_F_of_Q {i : ι} (h : i ∈ S.Q) : i ∈ F := (S.mem_Q.mp h).2

theorem card_Q_lt : (S.Q.filter fun i => (ev i).natDegree = mdeg F ev).card < mcnt F ev := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨S.iP, Finset.mem_filter.mpr ⟨S.hiP, S.hdeg⟩, fun h => ?_⟩
    exact (S.mem_Q.mp (Finset.mem_filter.mp h).1).1 rfl
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨S.mem_F_of_Q hi.1, hi.2⟩

theorem mord_Q_lt : mord S.Q ev < mord F ev :=
  mord_lt (fun i hi => natDegree_le_mdeg (S.mem_F_of_Q hi)) S.card_Q_lt

theorem natDegree_ev'_inr {i : ι} {j : ℕ} (hi : 0 < (ev i).natDegree) :
    (S.ev' (Sum.inr (i, j))).natDegree < (ev i).natDegree := by
  show (derivative^[j] (S.rem i)).natDegree < _
  exact lt_of_le_of_lt ((natDegree_iterate_derivative _ _).trans (Nat.sub_le _ _)) (S.hrem i hi).2

theorem mord_F'_lt : mord S.F' S.ev' < mord F ev := by
  apply mord_lt
  · rintro (i | ⟨i, j⟩) hx
    · exact natDegree_le_mdeg (S.mem_F_of_Q (mem_Fp_inl.mp hx))
    · have hx' := mem_Fp_inr.mp hx
      exact (S.natDegree_ev'_inr hx'.1.2).le.trans (natDegree_le_mdeg (S.mem_F_of_Q hx'.1.1))
  · refine lt_of_le_of_lt (le_trans (Finset.card_le_card ?_)
      (Finset.card_map (f := ⟨Sum.inl, Sum.inl_injective⟩) (s := S.Q.filter fun i => (ev i).natDegree = mdeg F ev)).le) S.card_Q_lt
    rintro (i | ⟨i, j⟩) hx
    · rw [Finset.mem_filter] at hx
      refine Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨mem_Fp_inl.mp hx.1, hx.2⟩, rfl⟩
    · exfalso
      rw [Finset.mem_filter] at hx
      have hx' := mem_Fp_inr.mp hx.1
      have h1 := S.natDegree_ev'_inr (j := j) hx'.1.2
      have h2 := natDegree_le_mdeg (ev := ev) (S.mem_F_of_Q hx'.1.1)
      rw [hx.2] at h1
      omega

theorem natDegree_peP {a : A} (ha : a ∈ B) : (pe (ev S.iP) a).natDegree = mdeg F ev := by
  rw [← S.hdeg]
  apply (pe_nrm (S.hN S.iP S.hiP a ha)).1

/-- The derivative witness of a member of `Q` is not `P`. -/
theorem dcl_Q : DCl S.Q ev B := by
  intro a ha i hi
  obtain ⟨j, hj, hje⟩ := S.hD a ha i (S.mem_F_of_Q hi)
  refine ⟨j, ?_, hje⟩
  refine S.mem_Q.mpr ⟨fun hjP => ?_, hj⟩
  subst hjP
  have h1 := S.natDegree_peP ha
  have h2 : (derivative (pe (ev i) a)).natDegree ≤ mdeg F ev - 1 :=
    (natDegree_derivative_le _).trans (Nat.sub_le_sub_right
      ((natDegree_map_le).trans (natDegree_le_mdeg (S.mem_F_of_Q hi))) 1)
  have h3 : (pe (ev S.iP) a).natDegree = (derivative (pe (ev i) a)).natDegree := by
    simp only at hje; rw [hje]
  have := S.hpos
  omega

theorem dcl_F' : DCl S.F' S.ev' B := by
  intro a ha x hx
  rcases x with i | ⟨i, j⟩
  · obtain ⟨j, hj, hje⟩ := S.dcl_Q a ha i (mem_Fp_inl.mp hx)
    exact ⟨Sum.inl j, mem_Fp_inl.mpr hj, hje⟩
  · have hx' := mem_Fp_inr.mp hx
    by_cases hjd : j < mdeg F ev
    · refine ⟨Sum.inr (i, j + 1), mem_Fp_inr.mpr ⟨hx'.1, by omega⟩, ?_⟩
      show pe (derivative^[j + 1] (S.rem i)) a = derivative (pe (derivative^[j] (S.rem i)) a)
      rw [pe_iterate_derivative, pe_iterate_derivative, Function.iterate_succ_apply']
    · refine ⟨Sum.inr (i, j), hx, ?_⟩
      have hz : derivative^[j] (S.rem i) = 0 := by
        apply iterate_derivative_eq_zero
        have := (S.hrem i hx'.1.2).2
        have := natDegree_le_mdeg (ev := ev) (S.mem_F_of_Q hx'.1.1)
        omega
      show pe (derivative^[j] (S.rem i)) a = derivative (pe (derivative^[j] (S.rem i)) a)
      rw [hz, pe_zero', derivative_zero]

/-- At a root of a nonconstant `q ∈ Q`, `P` has the sign of the remainder. -/
theorem sign_rem {a : A} (ha : a ∈ B) {q : ι} (hq : q ∈ S.Q) (hdq : 0 < (ev q).natDegree)
    {y : ℝ} (hy : (pe (ev q) a).eval y = 0) :
    SignType.sign ((pe (ev S.iP) a).eval y) = SignType.sign ((pe (S.rem q) a).eval y) := by
  have hne : ev q ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hdq; exact lt_irrefl _ hdq
  have hc : (((ev q).leadingCoeff : R) : A → ℝ) a ≠ 0 := by
    rcases S.hN q (S.mem_F_of_Q hq) a ha with h | h
    · exact h
    · exact absurd h hne
  exact sign_at_root hc (pe_identity (S.hrem q hdq).1 a) hy

end SD

end TSd

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-d (part 2): the per-parameter case analysis of one step.
Case A (some nonconstant `q ∈ Q` must vanish): replace `P` by its remainder.
Case B0 (a nonzero constant must vanish): empty.
Case C (only formally-zero members may vanish): the cell `C` of `Q` is an open interval on
which `P` is strictly monotone; realized signs of `P` are read off at the finite endpoints
(codes of `F'`, `T1`) and at `±∞` (leading coefficients, `T2`/`T3`). Appended to L4TE.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSd2

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

theorem iSign_erase_iff {κ : Type*} {F : Finset κ} {G : κ → ℝ[X]} {ν : κ → SignType} {k : κ}
    (hk : k ∈ F) {y : ℝ} :
    y ∈ iSign F G ν ↔ y ∈ iSign (F.erase k) G ν ∧ SignType.sign ((G k).eval y) = ν k := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (Finset.mem_of_mem_erase hi), h k hk⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases hik : i = k
    · subst hik; exact h2
    · exact h1 i (Finset.mem_erase.mpr ⟨hik, hi⟩)

theorem code_of_point {κ : Type*} (F' : Finset κ) (ev' : κ → R[X]) (a : A) (y : ℝ) :
    ∃ c ∈ codes F', a ∈ Rlz F' ev' c ∧
      ∀ x ∈ F', c x = SignType.sign ((pe (ev' x) a).eval y) := by
  obtain ⟨c, hc, hce⟩ := exists_code F' (fun x => SignType.sign ((pe (ev' x) a).eval y))
  exact ⟨c, hc, ⟨y, fun x hx => (hce x hx).symm⟩, hce⟩

theorem isOpen_sign_eq {f : ℝ → ℝ} (hf : Continuous f) {s : SignType} (hs : s ≠ 0) :
    IsOpen {y | SignType.sign (f y) = s} := by
  rcases s with _ | _ | _
  · exact absurd rfl hs
  · have : {y | SignType.sign (f y) = SignType.neg} = {y | f y < 0} := by
      ext y; simp only [mem_setOf_eq]; exact sign_eq_neg_one_iff
    rw [this]; exact isOpen_lt hf continuous_const
  · have : {y | SignType.sign (f y) = SignType.pos} = {y | 0 < f y} := by
      ext y; simp only [mem_setOf_eq]; exact sign_eq_one_iff
    rw [this]; exact isOpen_lt continuous_const hf

theorem isOpen_iSign {κ : Type*} {Q : Finset κ} {G : κ → ℝ[X]} {ν : κ → SignType}
    (h : ∀ i ∈ Q, ν i = 0 → G i = 0) : IsOpen (iSign Q G ν) := by
  have : iSign Q G ν = ⋂ i ∈ Q, {y | SignType.sign ((G i).eval y) = ν i} := by
    ext y; simp [iSign]
  rw [this]
  apply isOpen_biInter_finset
  intro i hi
  by_cases h0 : ν i = 0
  · have : {y | SignType.sign ((G i).eval y) = ν i} = univ := by
      ext y; simp [h i hi h0, h0]
    rw [this]; exact isOpen_univ
  · exact isOpen_sign_eq (G i).continuous h0

theorem ev_sign_iff {l : Filter ℝ} [l.NeBot] {f : ℝ → ℝ} {c : ℝ}
    (h : ∀ᶠ x in l, SignType.sign (f x) = SignType.sign c) (s : SignType) :
    (∀ᶠ x in l, SignType.sign (f x) = s) ↔ SignType.sign c = s := by
  constructor
  · intro h1
    obtain ⟨x, hx1, hx2⟩ := (h1.and h).exists
    rw [← hx2, hx1]
  · intro hc
    filter_upwards [h] with x hx
    rw [hx, hc]

theorem coe_negpow_mul (n : ℕ) (r : R) (a : A) :
    ((((-1 : R) ^ n * r : R)) : A → ℝ) a = (-1) ^ n * (r : A → ℝ) a := by
  simp

variable {F : Finset ι} {ev : ι → R[X]} {B : Set A}

namespace SD

variable (S : SD F ev B)

/-- Endpoint codes: relax `ν` on `Q`, one nonconstant `q` with strict code drops to `0`, and the
remainder of `P` by `q` has sign `s`. -/
def good (ν : ι → SignType) (s : SignType) (c : ι ⊕ (ι × ℕ) → SignType) : Prop :=
  (∀ i ∈ S.Q, Relax (ν i) (c (Sum.inl i))) ∧
    ∃ q ∈ S.Q, 0 < (ev q).natDegree ∧ ν q ≠ 0 ∧ c (Sum.inl q) = 0 ∧ c (Sum.inr (q, 0)) = s

theorem mem_F'_inl {i : ι} (hi : i ∈ S.Q) : Sum.inl i ∈ S.F' := mem_Fp_inl.mpr hi

theorem mem_F'_inr0 {q : ι} (hq : q ∈ S.Q) (hdq : 0 < (ev q).natDegree) :
    Sum.inr (q, 0) ∈ S.F' := mem_Fp_inr.mpr ⟨⟨hq, hdq⟩, Nat.succ_pos _⟩

theorem caseA_iff {ν : ι → SignType} {q : ι} (hq : q ∈ S.Q) (hνq : ν q = 0)
    (hdq : 0 < (ev q).natDegree) {a : A} (ha : a ∈ B) :
    a ∈ Rlz F ev ν ↔ ∃ c ∈ codes S.F',
      ((∀ i ∈ S.Q, c (Sum.inl i) = ν i) ∧ c (Sum.inr (q, 0)) = ν S.iP) ∧ a ∈ Rlz S.F' S.ev' c := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, hc, hRl, hcy⟩ := code_of_point S.F' S.ev' a y
    refine ⟨c, hc, ⟨fun i hi => ?_, ?_⟩, hRl⟩
    · rw [hcy _ (S.mem_F'_inl hi)]; exact hy i (S.mem_F_of_Q hi)
    · rw [hcy _ (S.mem_F'_inr0 hq hdq)]
      have hroot : (pe (ev q) a).eval y = 0 :=
        sign_eq_zero_iff.mp ((hy q (S.mem_F_of_Q hq)).trans hνq)
      show SignType.sign ((pe (S.rem q) a).eval y) = ν S.iP
      rw [← S.sign_rem ha hq hdq hroot]
      exact hy S.iP S.hiP
  · rintro ⟨c, -, ⟨h1, h2⟩, ⟨y, hy⟩⟩
    refine ⟨y, fun i hi => ?_⟩
    have hq' : SignType.sign ((pe (ev q) a).eval y) = c (Sum.inl q) := hy _ (S.mem_F'_inl hq)
    by_cases hiP : i = S.iP
    · subst hiP
      have hroot : (pe (ev q) a).eval y = 0 := sign_eq_zero_iff.mp (by rw [hq', h1 q hq, hνq])
      have h3 : SignType.sign ((pe (S.rem q) a).eval y) = c (Sum.inr (q, 0)) :=
        hy _ (S.mem_F'_inr0 hq hdq)
      show SignType.sign ((pe (ev S.iP) a).eval y) = ν S.iP
      rw [S.sign_rem ha hq hdq hroot, h3, h2]
    · have hiQ : i ∈ S.Q := S.mem_Q.mpr ⟨hiP, hi⟩
      have : SignType.sign ((pe (ev i) a).eval y) = c (Sum.inl i) := hy _ (S.mem_F'_inl hiQ)
      show SignType.sign ((pe (ev i) a).eval y) = ν i
      rw [this, h1 i hiQ]

theorem eval_pe_const {p : R[X]} {a : A} (hl : ((p.leadingCoeff : R) : A → ℝ) a ≠ 0)
    (hd : p.natDegree = 0) (y : ℝ) : (pe p a).eval y = ((p.leadingCoeff : R) : A → ℝ) a := by
  have hpn := pe_nrm (Or.inl hl)
  rw [eval_const (hpn.1.trans hd), ← hpn.2, leadingCoeff, hpn.1, hd]

theorem caseB0 {ν : ι → SignType} {q : ι} (hq : q ∈ S.Q) (hνq : ν q = 0)
    (hdq : (ev q).natDegree = 0) (hne : ev q ≠ 0) {a : A} (ha : a ∈ B) : a ∉ Rlz F ev ν := by
  rintro ⟨y, hy⟩
  have h1 := hy q (S.mem_F_of_Q hq)
  rcases S.hN q (S.mem_F_of_Q hq) a ha with hl | h0
  · simp only at h1
    rw [eval_pe_const hl hdq, hνq] at h1
    exact hl (sign_eq_zero_iff.mp h1)
  · exact hne h0

/-- The cell of `Q` at the parameter `a`. -/
def cell (ν : ι → SignType) (a : A) : Set ℝ := iSign S.Q (fun i => pe (ev i) a) ν

theorem rlz_iff_cell {ν : ι → SignType} {a : A} :
    a ∈ Rlz F ev ν ↔ ∃ y ∈ S.cell ν a, SignType.sign ((pe (ev S.iP) a).eval y) = ν S.iP := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, ((iSign_erase_iff S.hiP).mp hy).1, ((iSign_erase_iff S.hiP).mp hy).2⟩
  · rintro ⟨y, hy, hs⟩
    exact ⟨y, (iSign_erase_iff S.hiP).mpr ⟨hy, hs⟩⟩

theorem cell_ordConnected (ν : ι → SignType) {a : A} (ha : a ∈ B) : (S.cell ν a).OrdConnected :=
  (ithom (S.dcl_Q a ha) ν).1

theorem cell_isOpen {ν : ι → SignType} (hC : ∀ i ∈ S.Q, ν i = 0 → ev i = 0) (a : A) :
    IsOpen (S.cell ν a) :=
  isOpen_iSign fun i hi h0 => by show pe (ev i) a = 0; rw [hC i hi h0, pe_zero']

theorem cell_mono {ν : ι → SignType} (hC : ∀ i ∈ S.Q, ν i = 0 → ev i = 0) {a : A} (ha : a ∈ B) :
    StrictMonoOn (fun y => (pe (ev S.iP) a).eval y) (S.cell ν a) ∨
      StrictAntiOn (fun y => (pe (ev S.iP) a).eval y) (S.cell ν a) := by
  obtain ⟨j, hj, hje⟩ := S.hD a ha S.iP S.hiP
  simp only at hje
  have hdP := S.natDegree_peP ha
  have hpos := S.hpos
  have hjQ : j ∈ S.Q := by
    refine S.mem_Q.mpr ⟨fun hjP => ?_, hj⟩
    subst hjP
    have h2 : (derivative (pe (ev S.iP) a)).natDegree ≤ (pe (ev S.iP) a).natDegree - 1 :=
      natDegree_derivative_le _
    rw [← hje] at h2
    omega
  have hνj : ν j ≠ 0 := by
    intro h0
    have h1 := hC j hjQ h0
    rw [h1, pe_zero'] at hje
    have := derivative_eq_zero.mp hje.symm
    omega
  have hconv : Convex ℝ (S.cell ν a) := convex_iff_ordConnected.mpr (S.cell_ordConnected ν ha)
  have hcont : ContinuousOn (fun y => (pe (ev S.iP) a).eval y) (S.cell ν a) :=
    (pe (ev S.iP) a).continuous.continuousOn
  have hsgn : ∀ y ∈ S.cell ν a,
      SignType.sign ((derivative (pe (ev S.iP) a)).eval y) = ν j := by
    intro y hy
    rw [← hje]; exact hy j hjQ
  rcases hv : ν j with _ | _ | _
  · exact absurd hv hνj
  · right
    apply strictAntiOn_of_deriv_neg hconv hcont
    intro y hy
    have := hsgn y (interior_subset hy)
    rw [hv] at this
    rw [Polynomial.deriv]
    exact sign_eq_neg_one_iff.mp this
  · left
    apply strictMonoOn_of_deriv_pos hconv hcont
    intro y hy
    have := hsgn y (interior_subset hy)
    rw [hv] at this
    rw [Polynomial.deriv]
    exact sign_eq_one_iff.mp this

/-- `T1`: a finite endpoint of the cell with `sign P = s` is detected by an endpoint code. -/
theorem T1 {ν : ι → SignType} {a : A} (ha : a ∈ B) (s : SignType) :
    (∃ z ∈ closure (S.cell ν a), z ∉ S.cell ν a ∧
        SignType.sign ((pe (ev S.iP) a).eval z) = s) ↔
      (a ∈ Rlz S.Q ev ν ∧ ∃ c ∈ codes S.F', S.good ν s c ∧ a ∈ Rlz S.F' S.ev' c) := by
  constructor
  · rintro ⟨z, hzcl, hzC, hzs⟩
    have hne : (S.cell ν a).Nonempty := closure_nonempty_iff.mp ⟨z, hzcl⟩
    refine ⟨hne, ?_⟩
    have hzR := closure_iSign_subset _ _ _ hzcl
    obtain ⟨q, hq, hqne⟩ : ∃ q ∈ S.Q, SignType.sign ((pe (ev q) a).eval z) ≠ ν q := by
      by_contra hcon
      push Not at hcon
      exact hzC hcon
    have hq0 : SignType.sign ((pe (ev q) a).eval z) = 0 := (hzR q hq).resolve_left hqne
    have hνq : ν q ≠ 0 := fun h => hqne (hq0.trans h.symm)
    obtain ⟨x, hx⟩ := hne
    have hdq : 0 < (ev q).natDegree := by
      by_contra hd
      have hd0 : (ev q).natDegree = 0 := by omega
      rcases S.hN q (S.mem_F_of_Q hq) a ha with hl | h0
      · rw [eval_pe_const hl hd0] at hq0
        exact hl (sign_eq_zero_iff.mp hq0)
      · have := hx q hq
        simp only at this
        rw [h0, pe_zero', eval_zero, sign_zero] at this
        exact hνq this.symm
    obtain ⟨c, hc, hRl, hcz⟩ := code_of_point S.F' S.ev' a z
    refine ⟨c, hc, ⟨fun i hi => ?_, q, hq, hdq, hνq, ?_, ?_⟩, hRl⟩
    · rw [hcz _ (S.mem_F'_inl hi)]; exact hzR i hi
    · rw [hcz _ (S.mem_F'_inl hq)]; exact hq0
    · rw [hcz _ (S.mem_F'_inr0 hq hdq)]
      show SignType.sign ((pe (S.rem q) a).eval z) = s
      rw [← S.sign_rem ha hq hdq (sign_eq_zero_iff.mp hq0)]
      exact hzs
  · rintro ⟨⟨x, hx⟩, c, -, ⟨hrel, q, hq, hdq, hνq, hcq, hcs⟩, ⟨z, hz⟩⟩
    have hzR : z ∈ iRelax S.Q (fun i => pe (ev i) a) ν := by
      intro i hi
      have : SignType.sign ((pe (ev i) a).eval z) = c (Sum.inl i) := hz _ (S.mem_F'_inl hi)
      show Relax (ν i) (SignType.sign ((pe (ev i) a).eval z))
      rw [this]; exact hrel i hi
    have h2 : SignType.sign ((pe (ev q) a).eval z) = c (Sum.inl q) := hz _ (S.mem_F'_inl hq)
    have hroot : (pe (ev q) a).eval z = 0 := sign_eq_zero_iff.mp (h2.trans hcq)
    refine ⟨z, mem_closure_of_iRelax (ithom_relax (S.dcl_Q a ha) ⟨x, hx⟩) hx hzR, ?_, ?_⟩
    · intro hzC
      have h1 : SignType.sign ((pe (ev q) a).eval z) = ν q := hzC q hq
      rw [h2, hcq] at h1
      exact hνq h1.symm
    · have h3 : SignType.sign ((pe (S.rem q) a).eval z) = c (Sum.inr (q, 0)) :=
        hz _ (S.mem_F'_inr0 hq hdq)
      rw [S.sign_rem ha hq hdq hroot, h3, hcs]

/-- `T2`: the cell contains a neighbourhood of `+∞`. -/
theorem T2 {ν : ι → SignType} {a : A} (ha : a ∈ B) :
    (∀ᶠ y in atTop, y ∈ S.cell ν a) ↔
      ∀ i ∈ S.Q, ν i = SignType.sign ((((ev i).leadingCoeff : R) : A → ℝ) a) := by
  rw [cell, eventually_mem_iSign_atTop_iff]
  have h : ∀ i ∈ S.Q, (pe (ev i) a).leadingCoeff = (((ev i).leadingCoeff : R) : A → ℝ) a :=
    fun i hi => (pe_nrm (S.hN i (S.mem_F_of_Q hi) a ha)).2
  constructor
  · intro h1 i hi; rw [h1 i hi, h i hi]
  · intro h1 i hi; rw [h1 i hi, h i hi]

theorem lcN_eq {p : R[X]} {a : A} (h : ((p.leadingCoeff : R) : A → ℝ) a ≠ 0 ∨ p = 0) :
    ((pe p a).comp (-X)).leadingCoeff =
      ((((-1 : R) ^ p.natDegree * p.leadingCoeff : R)) : A → ℝ) a := by
  rw [leadingCoeff_comp_neg_X, coe_negpow_mul, (pe_nrm h).1, (pe_nrm h).2]

/-- `T3`: the cell contains a neighbourhood of `-∞`. -/
theorem T3 {ν : ι → SignType} {a : A} (ha : a ∈ B) :
    (∀ᶠ y in atBot, y ∈ S.cell ν a) ↔
      ∀ i ∈ S.Q, ν i =
        SignType.sign (((((-1 : R) ^ (ev i).natDegree * (ev i).leadingCoeff : R)) : A → ℝ) a) := by
  rw [cell, eventually_mem_iSign_atBot_iff]
  have h := fun i (hi : i ∈ S.Q) => lcN_eq (S.hN i (S.mem_F_of_Q hi) a ha)
  constructor
  · intro h1 i hi; rw [h1 i hi, h i hi]
  · intro h1 i hi; rw [h1 i hi, h i hi]

theorem P_atTop {a : A} (ha : a ∈ B) (s : SignType) :
    (∀ᶠ y in atTop, SignType.sign ((pe (ev S.iP) a).eval y) = s) ↔
      SignType.sign ((((ev S.iP).leadingCoeff : R) : A → ℝ) a) = s := by
  rw [← (pe_nrm (S.hN S.iP S.hiP a ha)).2]
  exact ev_sign_iff (eventually_sign_atTop _) s

theorem P_atBot {a : A} (ha : a ∈ B) (s : SignType) :
    (∀ᶠ y in atBot, SignType.sign ((pe (ev S.iP) a).eval y) = s) ↔
      SignType.sign (((((-1 : R) ^ (ev S.iP).natDegree * (ev S.iP).leadingCoeff : R)) :
        A → ℝ) a) = s := by
  rw [← lcN_eq (S.hN S.iP S.hiP a ha)]
  exact ev_sign_iff (eventually_sign_atBot _) s

end SD

end TSd2

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-d (part 3): assembly. One elimination step is SA given the
induction hypothesis on `Q` and `F'`; well-founded induction on `(max degree, count)` with
normalisation gives the **parametric one-variable Tarski–Seidenberg theorem** `ts`:
for a derivative-closed (at every parameter) finite family of polynomials in one variable with
coefficients in a subring `R` of `A → ℝ`, every realizable-sign-condition set
`{a | ∃ y, ∀ i ∈ F, sign ((pe (ev i) a).eval y) = ν i}` is in the Boolean algebra generated by
`{f > 0}`, `{f = 0}`, `f ∈ R`. Appended to L4TF.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSd3

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

theorem realized_sign_iff {C : Set ℝ} {f : ℝ → ℝ} (hC : C.OrdConnected) (hCo : IsOpen C)
    (hm : StrictMonoOn f C ∨ StrictAntiOn f C) (hf : Continuous f) {s : SignType} (hs : s ≠ 0) :
    (∃ y ∈ C, SignType.sign (f y) = s) ↔
      (∃ z ∈ closure C, z ∉ C ∧ SignType.sign (f z) = s) ∨
      ((∀ᶠ x in atTop, x ∈ C) ∧ ∀ᶠ x in atTop, SignType.sign (f x) = s) ∨
      ((∀ᶠ x in atBot, x ∈ C) ∧ ∀ᶠ x in atBot, SignType.sign (f x) = s) := by
  rcases s with _ | _ | _
  · exact absurd rfl hs
  · have := realized_neg_iff hC hCo hm hf
    simp only [show SignType.neg = -1 from rfl, sign_eq_neg_one_iff]
    exact this
  · have := realized_pos_iff hC hCo hm hf
    simp only [show SignType.pos = 1 from rfl, sign_eq_one_iff]
    exact this

theorem isSA_coe_sign (r : R) (s : SignType) : IsSA R {a : A | SignType.sign ((r : A → ℝ) a) = s} :=
  IsSA.sign r.2 s

variable {F : Finset ι} {ev : ι → R[X]} {B : Set A}

namespace SD

variable (S : SD F ev B)

/-- Parameters with a good endpoint code. -/
def U (ν : ι → SignType) (s : SignType) : Set A :=
  {a | ∃ c ∈ codes S.F', S.good ν s c ∧ a ∈ Rlz S.F' S.ev' c}

def TopS (ν : ι → SignType) : Set A :=
  {a | ∀ i ∈ S.Q, ν i = SignType.sign ((((ev i).leadingCoeff : R) : A → ℝ) a)}

def BotS (ν : ι → SignType) : Set A :=
  {a | ∀ i ∈ S.Q, ν i =
    SignType.sign (((((-1 : R) ^ (ev i).natDegree * (ev i).leadingCoeff : R)) : A → ℝ) a)}

def RealS (ν : ι → SignType) (s : SignType) : Set A :=
  (Rlz S.Q ev ν ∩ S.U ν s) ∪
    ((S.TopS ν ∩ {a | SignType.sign ((((ev S.iP).leadingCoeff : R) : A → ℝ) a) = s}) ∪
     (S.BotS ν ∩ {a | SignType.sign (((((-1 : R) ^ (ev S.iP).natDegree *
        (ev S.iP).leadingCoeff : R)) : A → ℝ) a) = s}))

theorem real_iff {ν : ι → SignType} (hC : ∀ i ∈ S.Q, ν i = 0 → ev i = 0) {a : A} (ha : a ∈ B)
    {s : SignType} (hs : s ≠ 0) :
    (∃ y ∈ S.cell ν a, SignType.sign ((pe (ev S.iP) a).eval y) = s) ↔ a ∈ S.RealS ν s := by
  refine (realized_sign_iff (S.cell_ordConnected ν ha) (S.cell_isOpen hC a) (S.cell_mono hC ha)
    (pe (ev S.iP) a).continuous hs).trans ?_
  beta_reduce
  rw [S.T1 ha s, S.T2 ha, S.P_atTop ha s, S.T3 ha, S.P_atBot ha s]
  exact Iff.rfl

theorem caseC_eq {ν : ι → SignType} (hC : ∀ i ∈ S.Q, ν i = 0 → ev i = 0) :
    B ∩ Rlz F ev ν = B ∩ (if ν S.iP = 0 then S.RealS ν 1 ∩ S.RealS ν (-1)
      else S.RealS ν (ν S.iP)) := by
  ext a
  simp only [mem_inter_iff]
  refine and_congr_right fun ha => ?_
  rw [S.rlz_iff_cell]
  split_ifs with h0
  · rw [h0, mem_inter_iff, ← S.real_iff hC ha one_ne_zero, ← S.real_iff hC ha (by decide)]
    simp only [sign_eq_zero_iff, sign_eq_one_iff, sign_eq_neg_one_iff]
    exact realized_zero_iff (S.cell_ordConnected ν ha) (S.cell_isOpen hC a) (S.cell_mono hC ha)
      (pe (ev S.iP) a).continuous
  · exact S.real_iff hC ha h0

theorem isSA_inter_union {X Y : Set A} (hX : IsSA R (B ∩ X)) (hY : IsSA R (B ∩ Y)) :
    IsSA R (B ∩ (X ∪ Y)) := by
  rw [inter_union_distrib_left]; exact hX.union hY

theorem isSA_inter_inter {X Y : Set A} (hX : IsSA R (B ∩ X)) (hY : IsSA R (B ∩ Y)) :
    IsSA R (B ∩ (X ∩ Y)) := by
  rw [inter_inter_distrib_left]; exact hX.inter hY

theorem isSA_RealS (hB : IsSA R B) (ν : ι → SignType) (hQ : IsSA R (B ∩ Rlz S.Q ev ν))
    (hF' : ∀ c, IsSA R (B ∩ Rlz S.F' S.ev' c)) (s : SignType) : IsSA R (B ∩ S.RealS ν s) := by
  have hU : IsSA R (B ∩ S.U ν s) := by
    have : B ∩ S.U ν s = ⋃ c ∈ (codes S.F').filter (S.good ν s), B ∩ Rlz S.F' S.ev' c := by
      ext a
      simp only [U, mem_inter_iff, mem_setOf_eq, mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · rintro ⟨hB', c, hc, hg, hR⟩; exact ⟨c, ⟨hc, hg⟩, hB', hR⟩
      · rintro ⟨c, ⟨hc, hg⟩, hB', hR⟩; exact ⟨hB', c, hc, hg, hR⟩
    rw [this]
    exact IsSA.biUnion _ fun c _ => hF' c
  have hTop : IsSA R (S.TopS ν) := by
    have : S.TopS ν = ⋂ i ∈ S.Q,
        {a : A | SignType.sign ((((ev i).leadingCoeff : R) : A → ℝ) a) = ν i} := by
      ext a; simp only [TopS, mem_setOf_eq, mem_iInter]
      exact forall₂_congr fun i _ => eq_comm
    rw [this]; exact IsSA.biInter _ fun i _ => isSA_coe_sign _ _
  have hBot : IsSA R (S.BotS ν) := by
    have : S.BotS ν = ⋂ i ∈ S.Q, {a : A | SignType.sign (((((-1 : R) ^ (ev i).natDegree *
        (ev i).leadingCoeff : R)) : A → ℝ) a) = ν i} := by
      ext a; simp only [BotS, mem_setOf_eq, mem_iInter]
      exact forall₂_congr fun i _ => eq_comm
    rw [this]; exact IsSA.biInter _ fun i _ => isSA_coe_sign _ _
  unfold RealS
  refine isSA_inter_union (isSA_inter_inter hQ hU) (isSA_inter_union ?_ ?_)
  · exact hB.inter (hTop.inter (isSA_coe_sign _ _))
  · exact hB.inter (hBot.inter (isSA_coe_sign _ _))

/-- **One elimination step.** -/
theorem ts_step (hB : IsSA R B) (ν : ι → SignType) (hQ : IsSA R (B ∩ Rlz S.Q ev ν))
    (hF' : ∀ c, IsSA R (B ∩ Rlz S.F' S.ev' c)) : IsSA R (B ∩ Rlz F ev ν) := by
  by_cases hA : ∃ q ∈ S.Q, ν q = 0 ∧ 0 < (ev q).natDegree
  · obtain ⟨q, hq, hνq, hdq⟩ := hA
    have : B ∩ Rlz F ev ν = ⋃ c ∈ (codes S.F').filter
        (fun c => (∀ i ∈ S.Q, c (Sum.inl i) = ν i) ∧ c (Sum.inr (q, 0)) = ν S.iP),
        B ∩ Rlz S.F' S.ev' c := by
      ext a
      simp only [mem_inter_iff, mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · rintro ⟨ha, hR⟩
        obtain ⟨c, hc, hcond, hR'⟩ := (S.caseA_iff hq hνq hdq ha).mp hR
        exact ⟨c, ⟨hc, hcond⟩, ha, hR'⟩
      · rintro ⟨c, ⟨hc, hcond⟩, ha, hR'⟩
        exact ⟨ha, (S.caseA_iff hq hνq hdq ha).mpr ⟨c, hc, hcond, hR'⟩⟩
    rw [this]
    exact IsSA.biUnion _ fun c _ => hF' c
  by_cases hB0 : ∃ q ∈ S.Q, ν q = 0 ∧ (ev q).natDegree = 0 ∧ ev q ≠ 0
  · obtain ⟨q, hq, hνq, hdq, hne⟩ := hB0
    have : B ∩ Rlz F ev ν = ∅ := by
      ext a
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      exact fun ha => S.caseB0 hq hνq hdq hne ha
    rw [this]; exact IsSA.empty
  have hC : ∀ i ∈ S.Q, ν i = 0 → ev i = 0 := by
    intro i hi h0
    by_contra hne
    have hd : (ev i).natDegree = 0 := by
      by_contra hd
      exact hA ⟨i, hi, h0, Nat.pos_of_ne_zero hd⟩
    exact hB0 ⟨i, hi, h0, hd, hne⟩
  rw [S.caseC_eq hC]
  split_ifs
  · exact isSA_inter_inter (S.isSA_RealS hB ν hQ hF' 1) (S.isSA_RealS hB ν hQ hF' (-1))
  · exact S.isSA_RealS hB ν hQ hF' _

end SD

/-- Base case: all members constant. -/
theorem ts_base {F : Finset ι} {ev : ι → R[X]} (hd : mdeg F ev = 0) (ν : ι → SignType) :
    IsSA R (Rlz (A := A) F ev ν) := by
  have hc : ∀ i ∈ F, ∀ (a : A) (y : ℝ),
      (pe (ev i) a).eval y = ((((ev i).coeff 0) : R) : A → ℝ) a := by
    intro i hi a y
    have h0 : (pe (ev i) a).natDegree = 0 := by
      have := (natDegree_map_le (p := ev i) (f := evR a)).trans (natDegree_le_mdeg hi)
      unfold pe; omega
    rw [eval_const h0, pe_coeff]
  have : Rlz (A := A) F ev ν =
      ⋂ i ∈ F, {a : A | SignType.sign (((((ev i).coeff 0) : R) : A → ℝ) a) = ν i} := by
    ext a
    simp only [Rlz, mem_setOf_eq, mem_iInter]
    constructor
    · rintro ⟨y, hy⟩ i hi
      rw [← hc i hi a y]; exact hy i hi
    · intro h
      exact ⟨0, fun i hi => by simp only; rw [hc i hi a 0]; exact h i hi⟩
  rw [this]
  exact IsSA.biInter _ fun i _ => isSA_coe_sign _ _

theorem ts_main : ∀ (o : ℕ ×ₗ ℕ) {κ : Type} (F : Finset κ) (ev : κ → R[X]), mord F ev ≤ o →
    ∀ B : Set A, IsSA R B → DCl F ev B → ∀ ν : κ → SignType, IsSA R (B ∩ Rlz F ev ν) := by
  intro o
  induction o using WellFoundedLT.induction with
  | _ o IH =>
    intro κ F ev hle B hB hD ν
    refine isSA_of_branches hB (mdeg F ev) (fun i hi => natDegree_le_mdeg hi) fun e => ?_
    set ev1 := evTr F ev (mdeg F ev) e with hev1
    set B1 := B ∩ BrE F ev (mdeg F ev) e with hB1def
    have hB1 : IsSA R B1 := hB.inter (isSA_BrE F ev _ e)
    have hN1 : Nrm F ev1 B1 := fun i hi a ha => nrm_evTr e i hi a ha.2
    have hD1 : DCl F ev1 B1 := dcl_evTr (fun i hi => natDegree_le_mdeg hi) hD e
    have hle1 : mord F ev1 ≤ o := (mord_mono fun i _ => natDegree_evTr_le e i).trans hle
    by_cases hd0 : mdeg F ev1 = 0
    · exact hB1.inter (ts_base hd0 ν)
    have hFne : F.Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      apply hd0; rw [mdeg, hem]; rfl
    obtain ⟨iP, hiP, hiPeq⟩ := Finset.exists_mem_eq_sup F hFne fun i => (ev1 i).natDegree
    obtain ⟨kk, ss, rem, hrem⟩ := exists_rem ev1 (ev1 iP)
    let S : SD F ev1 B1 :=
      { iP := iP, hiP := hiP, hdeg := hiPeq.symm, hpos := Nat.pos_of_ne_zero hd0,
        rem := rem, kk := kk, ss := ss, hrem := hrem, hN := hN1, hD := hD1 }
    exact S.ts_step hB1 ν
      (IH _ (lt_of_lt_of_le S.mord_Q_lt hle1) S.Q ev1 le_rfl B1 hB1 S.dcl_Q ν)
      (fun c => IH _ (lt_of_lt_of_le S.mord_F'_lt hle1) S.F' S.ev' le_rfl B1 hB1 S.dcl_F' c)

/-- **Parametric Tarski–Seidenberg in one variable** (derivative-closed families). -/
theorem ts {κ : Type} (F : Finset κ) (ev : κ → R[X])
    (hD : ∀ a : A, IDerivClosed F (fun i => pe (ev i) a)) (ν : κ → SignType) :
    IsSA R (Rlz (A := A) F ev ν) := by
  have := ts_main _ F ev le_rfl univ IsSA.univ (fun a _ => hD a) ν
  rwa [univ_inter] at this

end TSd3

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-e: Tarski–Seidenberg for an arbitrary finite family (close it under
derivatives first). Appended to L4TG.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSe

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)}

/-- **Parametric Tarski–Seidenberg in one variable**, any finite family. -/
theorem ts_any {κ : Type} (F : Finset κ) (ev : κ → R[X]) (ν : κ → SignType) :
    IsSA R (Rlz (A := A) F ev ν) := by
  set D := mdeg F ev
  set Ft : Finset (κ × ℕ) := F ×ˢ Finset.range (D + 2) with hFt
  set evt : κ × ℕ → R[X] := fun x => derivative^[x.2] (ev x.1) with hevt
  have hmem : ∀ i j, (i, j) ∈ Ft ↔ i ∈ F ∧ j < D + 2 := by
    intro i j; simp [hFt]
  have hDt : ∀ a : A, IDerivClosed Ft (fun x => pe (evt x) a) := by
    rintro a ⟨i, j⟩ hx
    have hx' := (hmem i j).mp hx
    by_cases hj : j < D + 1
    · refine ⟨(i, j + 1), (hmem i (j + 1)).mpr ⟨hx'.1, by omega⟩, ?_⟩
      show pe (derivative^[j + 1] (ev i)) a = derivative (pe (derivative^[j] (ev i)) a)
      rw [pe_iterate_derivative, pe_iterate_derivative, Function.iterate_succ_apply']
    · refine ⟨(i, j), hx, ?_⟩
      have hz : derivative^[j] (ev i) = 0 := by
        apply iterate_derivative_eq_zero
        have := natDegree_le_mdeg (ev := ev) hx'.1
        omega
      show pe (derivative^[j] (ev i)) a = derivative (pe (derivative^[j] (ev i)) a)
      rw [hz, pe_zero', derivative_zero]
  have h0mem : ∀ i ∈ F, (i, 0) ∈ Ft := fun i hi => (hmem i 0).mpr ⟨hi, by omega⟩
  have : Rlz (A := A) F ev ν =
      ⋃ c ∈ (codes Ft).filter (fun c => ∀ i ∈ F, c (i, 0) = ν i), Rlz Ft evt c := by
    ext a
    simp only [mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨c, hc, hRl, hcy⟩ := code_of_point Ft evt a y
      refine ⟨c, ⟨hc, fun i hi => ?_⟩, hRl⟩
      rw [hcy _ (h0mem i hi)]
      exact hy i hi
    · rintro ⟨c, ⟨-, hc⟩, ⟨y, hy⟩⟩
      refine ⟨y, fun i hi => ?_⟩
      have := hy (i, 0) (h0mem i hi)
      show SignType.sign ((pe (ev i) a).eval y) = ν i
      rw [← hc i hi]
      exact this
  rw [this]
  exact IsSA.biUnion _ fun c _ => ts Ft evt hDt c

end TSe

end SubanalyticLib


theorem solution {A : Type*} (R : Subring (A → ℝ)) {κ : Type} (F : Finset κ)
    (ev : κ → Polynomial R) (ν : κ → SignType) (Fam : Set (Set A))
    (hpos : ∀ f ∈ R, {a | 0 < f a} ∈ Fam) (hcompl : ∀ S ∈ Fam, Sᶜ ∈ Fam)
    (hinter : ∀ S ∈ Fam, ∀ T ∈ Fam, S ∩ T ∈ Fam) :
    {a : A | ∃ x : ℝ, ∀ i ∈ F, SignType.sign
      (((ev i).map ((Pi.evalRingHom (fun _ : A => ℝ) a).comp R.subtype)).eval x) = ν i} ∈ Fam := by
  have key : ∀ S : Set A, SubanalyticLib.IsSA R S → S ∈ Fam := by
    intro S hS
    induction hS with
    | pos hf => exact hpos _ hf
    | @zero f hf =>
      have e : {a | f a = 0} = ({a | 0 < f a}ᶜ ∩ {a | 0 < (-f) a}ᶜ) := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, Pi.neg_apply, not_lt]
        constructor
        · intro h
          exact ⟨h.le, by linarith⟩
        · rintro ⟨h1, h2⟩
          linarith
      rw [e]
      exact hinter _ (hcompl _ (hpos _ hf)) _ (hcompl _ (hpos _ (R.neg_mem hf)))
    | compl _ ih => exact hcompl _ ih
    | inter _ _ ih1 ih2 => exact hinter _ ih1 _ ih2
  exact key _ (SubanalyticLib.ts_any (A := A) (R := R) F ev ν)
