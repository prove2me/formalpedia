-- Prove2me | solution 1 for OAI.ParityWL.choice_of_balancedStar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:20:11.286541+00:00
-- url     : https://prove2.me/submissions/f63ee874-cb73-4c7f-9d9e-1b9da07fd85f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/ChoiceExtraction.lean:L67-L118
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.choice_of_balancedStar. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Theorems.Thm_OAI_ParityWL_BalancedStar_representatives
import Theorems.Thm_OAI_ParityWL_WeightedWitness_main_mass
import Theorems.Thm_OAI_ParityWL_WeightedWitness_mass_separator
import Theorems.Thm_OAI_ParityWL_WeightedWitness_testMass_transfer
import Theorems.Thm_OAI_ParityWL_baseType_inl_iff
import Theorems.Thm_OAI_ParityWL_baseType_inr_iff

-- ---- from OAI.Combinatorics.ParityLifts.Masses ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section Masses

open scoped Classical

variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

end Masses

section TemplateMass

open scoped Classical

variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t}

end TemplateMass

section BoundaryTests

open scoped Classical

variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

lemma WeightedWitness.testMass_add (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) (p q : W → Bit) :
    w.testMass Y u (p + q) = w.testMass Y u p + w.testMass Y u q := by
  unfold WeightedWitness.testMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : a x = u <;> simp [h, mul_add]

lemma WeightedWitness.testMass_one (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) : w.testMass Y u (fun _ => 1) = w.mass Y u := by
  simp [WeightedWitness.testMass, WeightedWitness.mass]

lemma WeightedWitness.testMass_zero (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) (p : W → Bit)
    (h : ∀ x ∈ Y, a x = u → p x = 0) : w.testMass Y u p = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  by_cases ha : a x = u <;> simp [ha, h x hx]

lemma WeightedWitness.testMass_complement (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) (p : W → Bit) :
    w.testMass Y u p + w.testMass Y u (fun x => 1 + p x) = w.mass Y u := by
  rw [← w.testMass_add]
  have he : p + (fun x => 1 + p x) = fun _ => (1 : Bit) := by
    funext x
    change p x + (1 + p x) = 1
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  rw [he, w.testMass_one]

/-- The global mismatch identity, including arbitrary zero representative weights. -/
lemma WeightedWitness.global_mismatch (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (p q : W → Bit)
    (hc : ∀ x y, F.Adj x y → a x = u → a y = v → p x + q y = 1) :
    w.testMass Finset.univ u p + w.testMass Finset.univ v q =
      w.mass Finset.univ u := by
  have ht := w.testMass_transfer huv.symm Finset.univ ∅ q (fun x => 1 + p x)
    (by simp) (by simp) (by simp) (by
      intro x y hxy hx hy
      have he := hc y x hxy.symm hy hx
      have hh := congrArg (fun e => p y + e) he
      simpa only [← add_assoc, CharTwo.add_self_eq_zero, zero_add, add_comm, add_zero] using hh)
  rw [ht, w.testMass_complement]

end BoundaryTests

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.BaseLabels ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section BaseLabels

open scoped Classical

variable {t : ℕ} (C : ChoiceSystem t)

lemma base_main_label (p : MainPair t) (d : C.Domain p.1.1) (e : C.Domain p.1.2)
    (h : (baseGraph C).Adj (.inl ⟨p.1.1, d⟩) (.inl ⟨p.1.2, e⟩)) :
    C.leftLabel p d = C.rightLabel p e := by
  have forward : ∀ (p' : MainPair t) (d' : C.Domain p'.1.1) (e' : C.Domain p'.1.2),
      (.inl ⟨p'.1.1, d'⟩ : BaseVertex C) = .inl ⟨p.1.1, d⟩ →
      (.inl ⟨p'.1.2, e'⟩ : BaseVertex C) = .inl ⟨p.1.2, e⟩ →
      C.leftLabel p' d' = C.rightLabel p' e' → C.leftLabel p d = C.rightLabel p e := by
    intro p' d' e' h0 h1 hlabel
    have hi : p'.1.1 = p.1.1 := Sum.inl.inj (congrArg baseType h0)
    have hj : p'.1.2 = p.1.2 := Sum.inl.inj (congrArg baseType h1)
    have hp : p' = p := Subtype.ext (Prod.ext hi hj)
    subst p'
    have hd : d' = d := by simpa using h0
    have he : e' = e := by simpa using h1
    simpa [hd, he] using hlabel
  generalize hx : (.inl ⟨p.1.1, d⟩ : BaseVertex C) = x at h
  generalize hy : (.inl ⟨p.1.2, e⟩ : BaseVertex C) = y at h
  rcases h.2 with h | h
  · cases h with
    | main p' d' e' he => exact forward p' d' e' hx.symm hy.symm he
    | left h' d' => cases hx
    | right h' e' => cases hx
    | third h' q' f' => cases hx
  · cases h with
    | main p' d' e' he =>
      have hi : p.1.1 = p'.1.2 := Sum.inl.inj (congrArg baseType hx)
      have hj : p.1.2 = p'.1.1 := Sum.inl.inj (congrArg baseType hy)
      have := p.property
      have := p'.property
      omega
    | left h' d' => cases hy
    | right h' e' => cases hy
    | third h' q' f' => cases hy

lemma base_helper_left_label (h : Helper t) (q : C.Label h.1.1)
    (d : C.Domain h.1.1.1.1)
    (ha : (baseGraph C).Adj (.inr ⟨h, q⟩) (.inl ⟨h.1.1.1.1, d⟩)) :
    q = C.leftLabel h.1.1 d := by
  generalize hx : (.inr ⟨h, q⟩ : BaseVertex C) = x at ha
  generalize hy : (.inl ⟨h.1.1.1.1, d⟩ : BaseVertex C) = y at ha
  rcases ha.2 with ha | ha
  · cases ha with
    | main p' d' e' he => cases hx
    | left h' d' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hq : q = C.leftLabel h.1.1 d' := by simpa using hx
      have hd : d = d' := by simpa using hy
      simpa [hd] using hq
    | right h' e' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hi : h.1.1.1.1 = h.1.1.1.2 := Sum.inl.inj (congrArg baseType hy)
      exact ((ne_of_lt h.1.1.2) hi).elim
    | third h' q' f' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hi : h.1.1.1.1 = h.1.2 := Sum.inl.inj (congrArg baseType hy)
      exact (h.2.1 hi.symm).elim
  · cases ha with
    | main p' d' e' he => cases hx
    | left h' d' => cases hx
    | right h' e' => cases hx
    | third h' q' f' => cases hx

lemma base_helper_right_label (h : Helper t) (q : C.Label h.1.1)
    (d : C.Domain h.1.1.1.2)
    (ha : (baseGraph C).Adj (.inr ⟨h, q⟩) (.inl ⟨h.1.1.1.2, d⟩)) :
    q = C.rightLabel h.1.1 d := by
  generalize hx : (.inr ⟨h, q⟩ : BaseVertex C) = x at ha
  generalize hy : (.inl ⟨h.1.1.1.2, d⟩ : BaseVertex C) = y at ha
  rcases ha.2 with ha | ha
  · cases ha with
    | main p' d' e' he => cases hx
    | right h' d' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hq : q = C.rightLabel h.1.1 d' := by simpa using hx
      have hd : d = d' := by simpa using hy
      simpa [hd] using hq
    | left h' e' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hi : h.1.1.1.2 = h.1.1.1.1 := Sum.inl.inj (congrArg baseType hy)
      exact ((ne_of_lt h.1.1.2) hi.symm).elim
    | third h' q' f' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hi : h.1.1.1.2 = h.1.2 := Sum.inl.inj (congrArg baseType hy)
      exact (h.2.2 hi.symm).elim
  · cases ha with
    | main p' d' e' he => cases hx
    | left h' d' => cases hx
    | right h' e' => cases hx
    | third h' q' f' => cases hx

lemma base_main_labels {x y : BaseVertex C} (p : MainPair t)
    (hxy : (baseGraph C).Adj x y) (hx : baseType x = .inl p.1.1)
    (hy : baseType y = .inl p.1.2) : leftLabelAt C p x = rightLabelAt C p y := by
  obtain ⟨d, rfl⟩ := (baseType_inl_iff C x p.1.1).mp hx
  obtain ⟨e, rfl⟩ := (baseType_inl_iff C y p.1.2).mp hy
  simp [base_main_label C p d e hxy]

lemma base_helper_left_labels {x y : BaseVertex C} (h : Helper t)
    (hxy : (baseGraph C).Adj x y) (hx : baseType x = .inr h)
    (hy : baseType y = .inl h.1.1.1.1) :
    helperLabelAt C h x = leftLabelAt C h.1.1 y := by
  obtain ⟨q, rfl⟩ := (baseType_inr_iff C x h).mp hx
  obtain ⟨d, rfl⟩ := (baseType_inl_iff C y h.1.1.1.1).mp hy
  simp [base_helper_left_label C h q d hxy]

lemma base_helper_right_labels {x y : BaseVertex C} (h : Helper t)
    (hxy : (baseGraph C).Adj x y) (hx : baseType x = .inr h)
    (hy : baseType y = .inl h.1.1.1.2) :
    helperLabelAt C h x = rightLabelAt C h.1.1 y := by
  obtain ⟨q, rfl⟩ := (baseType_inr_iff C x h).mp hx
  obtain ⟨d, rfl⟩ := (baseType_inl_iff C y h.1.1.1.2).mp hy
  simp [base_helper_right_label C h q d hxy]

end BaseLabels

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.BalancedBags ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section BalancedBags

open scoped Classical

variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t} {b : TemplateVertex t → Bit}

lemma sum_regions {n : ℕ} (region : W → Option (Fin n)) (f : W → Bit) :
    ∑ x, f x = (∑ x ∈ regionSet region none, f x) +
      ∑ i, ∑ x ∈ regionSet region (some i), f x := by
  rw [← Finset.sum_fiberwise Finset.univ region f, Fintype.sum_option]
  rfl

omit [Fintype W] in
lemma main_card_le (B : Finset W) (hp : ∀ i : Fin t, ∃ x ∈ B, a x = .inl i) :
    t ≤ B.card := by
  choose x hx ht using hp
  have hinj : Function.Injective x := by
    intro i j he
    have hh : Sum.inl i = (Sum.inl j : TemplateVertex t) :=
      (ht i).symm.trans ((congrArg a he).trans (ht j))
    exact Sum.inl.inj hh
  have hsub : Finset.univ.image x ⊆ B := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    exact hx i
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hc

omit [Fintype W] in
lemma missing_main (B : Finset W) (hB : B.card < t) :
    ∃ i : Fin t, ∀ x ∈ B, a x ≠ .inl i := by
  by_contra h
  push Not at h
  have h' := main_card_le (a := a) B h
  omega

end BalancedBags

section MismatchPredicates

open scoped Classical

variable {t : ℕ} (C : ChoiceSystem t) {W : Type} {F : SimpleGraph W}
variable (φ : F →g baseGraph C)

lemma test_main_compatible (p : MainPair t) (α : C.Label p) {x y : W}
    (hxy : F.Adj x y) (hx : baseType (φ x) = .inl p.1.1)
    (hy : baseType (φ y) = .inl p.1.2) :
    leftTest C φ p α x + rightTest C φ p α y = 1 := by
  have he := base_main_labels C p (φ.map_adj hxy) hx hy
  unfold leftTest rightTest
  rw [he]
  split_ifs <;> simp

lemma test_helper_left_compatible (h : Helper t) (α : C.Label h.1.1) {x y : W}
    (hxy : F.Adj x y) (hx : baseType (φ x) = .inl h.1.1.1.1)
    (hy : baseType (φ y) = .inr h) :
    leftTest C φ h.1.1 α x = helperTest C φ h α y := by
  have he := base_helper_left_labels C h (φ.map_adj hxy.symm) hy hx
  unfold leftTest helperTest
  rw [he]

lemma test_helper_right_compatible (h : Helper t) (α : C.Label h.1.1) {x y : W}
    (hxy : F.Adj x y) (hx : baseType (φ x) = .inl h.1.1.1.2)
    (hy : baseType (φ y) = .inr h) :
    rightTest C φ h.1.1 α x = 1 + helperTest C φ h α y := by
  have he := base_helper_right_labels C h (φ.map_adj hxy.symm) hy hx
  unfold rightTest helperTest
  rw [he]
  split_ifs <;> simp [CharTwo.add_self_eq_zero]

lemma bit_complement_left {x y : Bit} (h : x + y = 1) : x = 1 + y := by
  have he := congrArg (· + y) h
  simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero] using he

lemma bit_complement_right {x y : Bit} (h : x + y = 1) : y = 1 + x :=
  bit_complement_left (by rwa [add_comm])

end MismatchPredicates

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.ChoiceExtraction ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section ChoiceFromBalancedStar

open scoped Classical

variable {t : ℕ} (C : ChoiceSystem t) {W : Type} [Fintype W]
variable {F : SimpleGraph W} (φ : F →g baseGraph C)
variable (w : WeightedWitness (template t) F ((baseProjection C).comp φ) (starParity t))

lemma mismatch_side_zero (p : MainPair t) (α : C.Label p) (Y S : Finset W)
    (hb : ∀ x ∈ Y, ∀ y, F.Adj x y → y ∉ Y → y ∈ S)
    (hn : ∀ x ∈ S, ∀ h : Helper t, baseType (φ x) ≠ .inr h)
    (hp : ∀ x ∈ S, baseType (φ x) = .inl p.1.1 → leftTest C φ p α x = 0)
    (hq : ∀ x ∈ S, baseType (φ x) = .inl p.1.2 → rightTest C φ p α x = 0)
    (ℓ : Fin t) (hℓ : ∀ x ∈ S, baseType (φ x) ≠ .inl ℓ)
    (hm : w.mass Y (.inl ℓ) = 0) :
    w.testMass Y (.inl p.1.1) (leftTest C φ p α) +
      w.testMass Y (.inl p.1.2) (rightTest C φ p α) = 0 := by
  by_cases hi : ℓ = p.1.1
  · subst ℓ
    have ht := w.testMass_transfer
      (u := .inl p.1.2) (v := .inl p.1.1) (Ne.symm (ne_of_lt p.2))
      Y S (rightTest C φ p α) (fun x => 1 + leftTest C φ p α x) hb hℓ hq (by
        intro x y he hx hy
        exact bit_complement_right (test_main_compatible C φ p α he.symm hy hx))
    rw [ht, w.testMass_complement, hm]
  · by_cases hj : ℓ = p.1.2
    · subst ℓ
      have ht := w.testMass_transfer
        (u := .inl p.1.1) (v := .inl p.1.2) (ne_of_lt p.2)
        Y S (leftTest C φ p α) (fun x => 1 + rightTest C φ p α x) hb hℓ hp (by
          intro x y he hx hy
          exact bit_complement_left (test_main_compatible C φ p α he hx hy))
      rw [ht, add_comm, w.testMass_complement, hm]
    · let h : Helper t := ⟨(p, ℓ), hi, hj⟩
      have hh : ∀ x ∈ S, ((baseProjection C).comp φ) x ≠ .inr h :=
        fun x hx => hn x hx h
      have ht₀ := w.testMass_transfer
        (u := .inl p.1.1) (v := .inr h) (Or.inl rfl)
        Y S (leftTest C φ p α) (helperTest C φ h α) hb hh hp (by
          intro x y he hx hy
          exact test_helper_left_compatible C φ h α he hx hy)
      have ht₁ := w.testMass_transfer
        (u := .inl p.1.2) (v := .inr h) (Or.inr (Or.inl rfl))
        Y S (rightTest C φ p α) (fun x => 1 + helperTest C φ h α x) hb hh hq (by
          intro x y he hx hy
          exact test_helper_right_compatible C φ h α he hx hy)
      have hmass := w.mass_separator
        (u := .inr h) (v := .inl ℓ) (Or.inr (Or.inr rfl)) Y S hb hh hℓ
      rw [ht₀, ht₁, w.testMass_complement, hmass, hm]

lemma BalancedStar.partition_testMass
    (s : BalancedStar w) (u : TemplateVertex t) (p : W → Bit) :
    w.testMass Finset.univ u p = w.testMass s.bag u p +
      ∑ i, w.testMass (regionSet s.region (some i)) u p := by
  rw [s.bag_eq]
  exact sum_regions s.region (fun x => @ite Bit (((baseProjection C).comp φ) x = u)
    (Classical.propDecidable _) (w.vertex x * p x) 0)

/-- The helper boundary argument from a finite partition around a balanced bag. -/
theorem choice_of_balancedStar (s : BalancedStar w) (ht : 0 < t) : C.Successful := by
  obtain ⟨xs, htype, hbag⟩ := s.representatives w ht
  have hd' : ∀ i : Fin t, ∃ d : C.Domain i, φ (xs i) = .inl ⟨i, d⟩ := by
    intro i
    exact (baseType_inl_iff C (φ (xs i)) i).mp (htype i)
  choose d hd using hd'
  refine ⟨d, ?_⟩
  intro p
  by_contra hneq
  let α := C.leftLabel p (d p.1.1)
  have hp : ∀ x ∈ s.bag, baseType (φ x) = .inl p.1.1 →
      leftTest C φ p α x = 0 := by
    intro x hx hx'
    rw [hbag] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hi : i = p.1.1 := Sum.inl.inj ((htype i).symm.trans hx')
    subst i
    simp [leftTest, hd, α]
  have hq : ∀ x ∈ s.bag, baseType (φ x) = .inl p.1.2 →
      rightTest C φ p α x = 0 := by
    intro x hx hx'
    rw [hbag] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hi : i = p.1.2 := Sum.inl.inj ((htype i).symm.trans hx')
    subst i
    simp [rightTest, hd, α, Ne.symm hneq]
  have hn : ∀ x ∈ s.bag, ∀ h : Helper t, baseType (φ x) ≠ .inr h := by
    intro x hx h he
    rw [hbag] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hh := (htype i).symm.trans he
    cases hh
  have ho : ∀ j, w.testMass (regionSet s.region (some j)) (.inl p.1.1)
      (leftTest C φ p α) + w.testMass (regionSet s.region (some j)) (.inl p.1.2)
      (rightTest C φ p α) = 0 := by
    intro j
    obtain ⟨ℓ, hℓ⟩ := missing_main (a := (baseProjection C).comp φ)
      (s.separator j) (s.separator_small j)
    exact mismatch_side_zero C φ w p α _ _ (s.boundary j)
      (fun x hx => hn x (s.separator_sub j hx))
      (fun x hx => hp x (s.separator_sub j hx))
      (fun x hx => hq x (s.separator_sub j hx)) ℓ hℓ (s.zero_mass j ℓ hℓ)
  have hglobal := w.global_mismatch (u := .inl p.1.1) (v := .inl p.1.2)
    (ne_of_lt p.2) (leftTest C φ p α) (rightTest C φ p α)
    (fun _ _ he hx hy => test_main_compatible C φ p α he hx hy)
  rw [w.main_mass ht p.1.1, s.partition_testMass C φ w, s.partition_testMass C φ w,
    w.testMass_zero s.bag (.inl p.1.1) _ hp,
    w.testMass_zero s.bag (.inl p.1.2) _ hq, zero_add, zero_add,
    ← Finset.sum_add_distrib] at hglobal
  simp only [ho, Finset.sum_const_zero] at hglobal
  exact zero_ne_one hglobal

end ChoiceFromBalancedStar

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.choice_of_balancedStar := @_root_.OAI.ParityWL.choice_of_balancedStar
