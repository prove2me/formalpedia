-- Prove2me | solution 1 for MDPFinance.Stationary.card_game_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:43:09.025205+00:00
-- url     : https://prove2.me/submissions/80c082fe-31b2-4a85-9451-e69ce506e537

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators
import Definitions.Def_MDPFinance_Stationary_ValueFunction

open MeasureTheory ProbabilityTheory
open MDPFinance.Stationary

namespace CardAux

lemma sup_toENN (y : ℝ) : ((y : EReal) ⊔ 0).toENNReal = ENNReal.ofReal y := by
  rcases le_total y 0 with h | h
  · rw [sup_of_le_right (by exact_mod_cast h)]
    simp [ENNReal.ofReal_of_nonpos h]
  · rw [sup_of_le_left (by exact_mod_cast h)]
    rfl

lemma neg_sup_toENN (y : ℝ) : ((-(y : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-y) := by
  rw [← EReal.coe_neg]; exact sup_toENN _

lemma fin_sub (s t : ENNReal) (hs : s ≠ ⊤) (ht : t ≠ ⊤) :
    (s : EReal) + -(t : EReal) = ((s.toReal - t.toReal : ℝ) : EReal) := by
  rw [← EReal.coe_ennreal_toReal hs, ← EReal.coe_ennreal_toReal ht]
  rw [← EReal.coe_neg, ← EReal.coe_add, sub_eq_add_neg]

lemma ei_two {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a c : α) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (v : α → EReal) (y1 y2 : ℝ)
    (h1 : v a = y1) (h2 : v c = y2) :
    erealIntegral (ENNReal.ofReal p • Measure.dirac a + ENNReal.ofReal q • Measure.dirac c) v
      = ((p * y1 + q * y2 : ℝ) : EReal) := by
  unfold erealIntegral
  simp only [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, h1, h2,
    sup_toENN, neg_sup_toENN]
  simp only [smul_eq_mul]
  rw [fin_sub _ _ (by finiteness) (by finiteness)]
  congr 1
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq,
    ENNReal.toReal_ofReal', ]
  rcases le_total y1 0 with h | h <;> rcases le_total y2 0 with h' | h' <;>
    simp [h, h'] <;> ring

lemma ei_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) (v : α → EReal) (y : ℝ) (h : v a = y) :
    erealIntegral (Measure.dirac a) v = (y : EReal) := by
  have := ei_two a a 1 0 zero_le_one le_rfl v y y h h
  simpa using this

lemma meas_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (μ : Measure α) [IsProbabilityMeasure μ] (a : α) (h : μ {a} = 1) :
    μ = Measure.dirac a := by
  rw [Measure.ext_iff_singleton]
  intro x
  by_cases hx : x = a
  · subst hx; simp [h]
  · rw [Measure.dirac_apply' _ (measurableSet_singleton x)]
    have hc : μ {a}ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff (measurableSet_singleton a)]; exact h
    have : ({x} : Set α) ⊆ {a}ᶜ := by simpa using Ne.symm hx
    have hx' : a ∉ ({x} : Set α) := fun h => hx (Set.mem_singleton_iff.mp h).symm
    rw [Set.indicator_of_notMem hx']
    exact measure_mono_null this hc


noncomputable def G (x : ℕ × ℕ) : ℝ := ((x.1 : ℝ) - x.2) / ((x.1 : ℝ) + x.2)

lemma main (M : StationaryMarkovDecisionModel (ℕ × ℕ) Bool)
    (hD : ∀ x a, (x, a) ∈ M.D ↔ (x ≠ (0, 1) ∧ x ≠ (1, 0)) ∨ a = true)
    (hQ_red : ∀ b r : ℕ, 1 ≤ r → M.Q ((b, r), false) {(b, r - 1)} = ENNReal.ofReal (r / (r + b) : ℝ))
    (hQ_black : ∀ b r : ℕ, 1 ≤ b →
      M.Q ((b, r), false) {(b - 1, r)} = ENNReal.ofReal (b / (r + b) : ℝ))
    (hQ_stop : ∀ x : ℕ × ℕ, M.Q (x, true) {((0 : ℕ), (0 : ℕ))} = 1)
    (hQ_absorb : ∀ a : Bool, M.Q (((0 : ℕ), (0 : ℕ)), a) {((0 : ℕ), (0 : ℕ))} = 1)
    (hr_stop : ∀ x, M.r (x, true) = G x)
    (hr_go : ∀ x : ℕ × ℕ, M.r (x, false) = 0)
    (hg : ∀ x, M.g x = G x)
    (hβ : M.β = 1) :
    ∀ k (π : ℕ → (ℕ × ℕ) → Bool), IsPolicySeq M k π → ∀ b r : ℕ, b + r ≤ k → ∀ acc : ℝ,
      EFromToAcc M π (fun x => (M.g x : EReal)) k (b, r) (acc : EReal) 1
        = ((acc + G (b, r) : ℝ) : EReal) := by
  have hprob : ∀ xa, IsProbabilityMeasure (M.Q xa) := M.hQ_prob
  have G00 : G (0, 0) = 0 := by simp [G]
  intro k
  induction k with
  | zero =>
    intro π _ b r hbr acc
    obtain ⟨rfl, rfl⟩ : b = 0 ∧ r = 0 := by omega
    simp [EFromToAcc, hg, G00]
  | succ k ih =>
    intro π hπ b r hbr acc
    have hπ' : IsPolicySeq M k (fun j => π (j + 1)) := fun j hj => hπ (j + 1) (by omega)
    have hdisc : (1 : ℝ) * M.β = 1 := by simp [hβ]
    have hmem : ((b, r), π 0 (b, r)) ∈ M.D := (hπ 0 (by omega)).2 _
    rw [EFromToAcc, hdisc]
    have hacc : ∀ a, (acc : EReal) + ((1 : ℝ) : EReal) * (M.r ((b, r), a) : EReal)
        = ((acc + M.r ((b, r), a) : ℝ) : EReal) := by
      intro a; simp
    rw [hacc]
    have IH : ∀ b' r' : ℕ, b' + r' ≤ k → ∀ acc' : ℝ,
        EFromToAcc M (fun j => π (j + 1)) (fun x => (M.g x : EReal)) k (b', r') (acc' : EReal) 1
          = ((acc' + G (b', r') : ℝ) : EReal) := fun b' r' h acc' => ih _ hπ' b' r' h acc'
    generalize ha : π 0 (b, r) = a at hmem ⊢
    cases a with
    | true =>
      rw [meas_dirac _ _ (hQ_stop _)]
      refine (ei_dirac _ _ (acc + M.r ((b, r), true) + G (0, 0)) ?_).trans ?_
      · exact IH 0 0 (by omega) _
      · simp [hr_stop, G00]
    | false =>
      have hne : (b, r) ≠ (0, 1) ∧ (b, r) ≠ (1, 0) := by
        rcases (hD _ _).1 hmem with h | h
        · exact h
        · exact absurd h (by decide)
      rw [hr_go, add_zero]
      rcases Nat.eq_zero_or_pos b with hb | hb <;> rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hb; subst hr
        rw [meas_dirac _ _ (hQ_absorb _)]
        exact ei_dirac _ _ (acc + G (0, 0)) (IH 0 0 (by omega) _)
      · subst hb
        have hr2 : 2 ≤ r := by
          rcases Nat.lt_or_ge r 2 with h | h
          · exfalso; apply hne.1; ext <;> simp; omega
          · exact h
        have h1 : M.Q (((0 : ℕ), r), false) {((0 : ℕ), r - 1)} = 1 := by
          have : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          rw [hQ_red 0 r hr]; simp [this]
        rw [meas_dirac _ _ h1]
        refine (ei_dirac _ _ (acc + G (0, r - 1)) ?_).trans ?_
        · exact IH 0 (r - 1) (by omega) _
        congr 1
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
        simp only [G]
        push_cast
        have : (0 : ℝ) < r' + 1 := by positivity
        field_simp
        ring
      · subst hr
        have hb2 : 2 ≤ b := by
          rcases Nat.lt_or_ge b 2 with h | h
          · exfalso; apply hne.2; ext <;> simp; omega
          · exact h
        have h1 : M.Q ((b, (0 : ℕ)), false) {(b - 1, (0 : ℕ))} = 1 := by
          have : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          rw [hQ_black b 0 hb]; simp [this]
        rw [meas_dirac _ _ h1]
        refine (ei_dirac _ _ (acc + G (b - 1, 0)) ?_).trans ?_
        · exact IH (b - 1) 0 (by omega) _
        congr 1
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
        simp only [G]
        push_cast
        have : (0 : ℝ) < b' + 1 := by positivity
        field_simp
        ring
      · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have hpos : (0 : ℝ) < (r' + 1 : ℕ) + (b' + 1 : ℕ) := by positivity
        have hμ : M.Q ((b' + 1, r' + 1), false)
            = ENNReal.ofReal (((r' + 1 : ℕ) : ℝ) / ((r' + 1 : ℕ) + (b' + 1 : ℕ))) •
                Measure.dirac (b' + 1, r') +
              ENNReal.ofReal (((b' + 1 : ℕ) : ℝ) / ((r' + 1 : ℕ) + (b' + 1 : ℕ))) •
                Measure.dirac (b', r' + 1) := by
          have hR := hQ_red (b' + 1) (r' + 1) (by omega)
          have hB := hQ_black (b' + 1) (r' + 1) (by omega)
          simp only [Nat.add_sub_cancel] at hR hB
          have hne2 : ((b' + 1, r') : ℕ × ℕ) ≠ (b', r' + 1) := by
            intro h; simp at h
          have hsum : M.Q ((b' + 1, r' + 1), false) {(b' + 1, r'), (b', r' + 1)} = 1 := by
            rw [Set.insert_eq, measure_union (by simp [hne2]) (measurableSet_singleton _),
              hR, hB, ← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div]
            rw [div_self hpos.ne', ENNReal.ofReal_one]
          have hcompl : M.Q ((b' + 1, r' + 1), false) {(b' + 1, r'), (b', r' + 1)}ᶜ = 0 := by
            rw [prob_compl_eq_zero_iff (by measurability)]; exact hsum
          rw [Measure.ext_iff_singleton]
          intro x
          simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
          rw [Measure.dirac_apply' _ (measurableSet_singleton x),
            Measure.dirac_apply' _ (measurableSet_singleton x)]
          by_cases h1 : x = (b' + 1, r')
          · subst h1
            rw [Set.indicator_of_mem (Set.mem_singleton _),
              Set.indicator_of_notMem (by simp [hne2.symm]), hR]
            simp
          by_cases h2 : x = (b', r' + 1)
          · subst h2
            rw [Set.indicator_of_mem (Set.mem_singleton _),
              Set.indicator_of_notMem (by simp [hne2]), hB]
            simp
          rw [Set.indicator_of_notMem (by simpa using Ne.symm h1),
            Set.indicator_of_notMem (by simpa using Ne.symm h2)]
          simp only [mul_zero, add_zero]
          apply measure_mono_null _ hcompl
          intro y hy
          simp only [Set.mem_singleton_iff] at hy
          subst hy
          simp [h1, h2]
        rw [hμ]
        refine (ei_two _ _ _ _ ?_ ?_ _ (acc + G (b' + 1, r'))
          (acc + G (b', r' + 1)) ?_ ?_).trans ?_
        · positivity
        · positivity
        · exact IH (b' + 1) r' (by omega) acc
        · exact IH b' (r' + 1) (by omega) acc
        congr 1
        simp only [G]
        push_cast at hpos ⊢
        have h3 : (0 : ℝ) < (b' : ℝ) + 1 + r' := by positivity
        have h4 : (0 : ℝ) < (b' : ℝ) + (r' + 1) := by positivity
        field_simp
        ring

end CardAux

theorem solution (M : StationaryMarkovDecisionModel (ℕ × ℕ) Bool)
    (hD : ∀ x a, (x, a) ∈ M.D ↔ (x ≠ (0, 1) ∧ x ≠ (1, 0)) ∨ a = true)
    (hQ_red : ∀ b r : ℕ, 1 ≤ r → M.Q ((b, r), false) {(b, r - 1)} = ENNReal.ofReal (r / (r + b) : ℝ))
    (hQ_black : ∀ b r : ℕ, 1 ≤ b →
      M.Q ((b, r), false) {(b - 1, r)} = ENNReal.ofReal (b / (r + b) : ℝ))
    (hQ_stop : ∀ x : ℕ × ℕ, M.Q (x, true) {((0 : ℕ), (0 : ℕ))} = 1)
    (hQ_absorb : ∀ a : Bool, M.Q (((0 : ℕ), (0 : ℕ)), a) {((0 : ℕ), (0 : ℕ))} = 1)
    (hr_stop : ∀ b r : ℕ, (b, r) ≠ (0, 0) →
      M.r ((b, r), true) = ((b : ℝ) - (r : ℝ)) / ((b : ℝ) + (r : ℝ)))
    (hr_stop_G : M.r (((0 : ℕ), (0 : ℕ)), true) = 0)
    (hr_go : ∀ x : ℕ × ℕ, M.r (x, false) = 0)
    (hg : ∀ b r : ℕ, (b, r) ≠ (0, 0) → M.g (b, r) = ((b : ℝ) - (r : ℝ)) / ((b : ℝ) + (r : ℝ)))
    (hg_G : M.g (0, 0) = 0)
    (hβ : M.β = 1) (b0 r0 : ℕ) :
    J M (r0 + b0) (b0, r0) = (M.g (b0, r0) : EReal) ∧
      M.g (b0, r0) = ((b0 : ℝ) - (r0 : ℝ)) / ((b0 : ℝ) + (r0 : ℝ)) ∧
      ∀ π : ℕ → (ℕ × ℕ) → Bool, IsPolicySeq M (r0 + b0) π →
        Jpi M π (r0 + b0) (b0, r0) = J M (r0 + b0) (b0, r0) := by
  have hg' : ∀ x, M.g x = CardAux.G x := by
    rintro ⟨b, r⟩
    by_cases h : (b, r) = (0, 0)
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [hg_G, CardAux.G]
    · rw [hg b r h]; rfl
  have hr' : ∀ x, M.r (x, true) = CardAux.G x := by
    rintro ⟨b, r⟩
    by_cases h : (b, r) = (0, 0)
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [hr_stop_G, CardAux.G]
    · rw [hr_stop b r h]; rfl
  have key : ∀ π, IsPolicySeq M (r0 + b0) π →
      Jpi M π (r0 + b0) (b0, r0) = (M.g (b0, r0) : EReal) := by
    intro π hπ
    have := CardAux.main M hD hQ_red hQ_black hQ_stop hQ_absorb hr' hr_go hg' hβ
      (r0 + b0) π hπ b0 r0 (by omega) 0
    simp only [EReal.coe_zero, zero_add] at this
    rw [Jpi, this, hg']
  have hJ : J M (r0 + b0) (b0, r0) = (M.g (b0, r0) : EReal) := by
    obtain ⟨f, hf, hfD⟩ := M.hD_sel
    have hπ0 : IsPolicySeq M (r0 + b0) (fun _ => f) := fun _ _ => ⟨hf, hfD⟩
    apply le_antisymm
    · exact iSup₂_le fun π hπ => (key π hπ).le
    · exact (key _ hπ0).symm.le.trans (le_iSup₂ (f := fun π (_ : π ∈ {π | IsPolicySeq M (r0 + b0) π}) =>
        Jpi M π (r0 + b0) (b0, r0)) (fun _ => f) hπ0)
  refine ⟨hJ, by rw [hg']; rfl, fun π hπ => by rw [key π hπ, hJ]⟩
