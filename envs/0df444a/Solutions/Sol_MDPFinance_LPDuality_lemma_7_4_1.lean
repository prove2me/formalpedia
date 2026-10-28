-- Prove2me | solution 1 for MDPFinance.LPDuality.lemma_7_4_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:09:34.265985+00:00
-- url     : https://prove2.me/submissions/21d50f48-ff9e-4d4b-9a7e-8da3e49e9ae5

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value

open MeasureTheory ProbabilityTheory Filter
open MDPFinance.LPDuality

namespace L741Aux

lemma erealIntegral_mono {E : Type*} [MeasurableSpace E] (μ : Measure E) {f g : E → EReal}
    (h : ∀ x, f x ≤ g x) : erealIntegral μ f ≤ erealIntegral μ g := by
  unfold erealIntegral
  apply add_le_add
  · apply EReal.coe_ennreal_le_coe_ennreal_iff.2
    apply lintegral_mono
    intro x
    exact EReal.toENNReal_le_toENNReal (sup_le_sup_right (h x) _)
  · apply EReal.neg_le_neg_iff.2
    apply EReal.coe_ennreal_le_coe_ennreal_iff.2
    apply lintegral_mono
    intro x
    exact EReal.toENNReal_le_toENNReal (sup_le_sup_right (EReal.neg_le_neg_iff.2 (h x)) _)

lemma erealIntegral_of_nonneg {E : Type*} [MeasurableSpace E] (μ : Measure E) {g : E → EReal}
    (hg : ∀ x, 0 ≤ g x) :
    erealIntegral μ g = ((∫⁻ x, (g x ⊔ 0).toENNReal ∂μ : ENNReal) : EReal) := by
  unfold erealIntegral
  have : ∀ x, ((-g x) ⊔ 0).toENNReal = 0 := fun x => by
    rw [sup_of_le_right (by simpa using hg x)]; simp
  simp [this]

lemma erealIntegral_nonneg {E : Type*} [MeasurableSpace E] (μ : Measure E) {g : E → EReal}
    (hg : ∀ x, 0 ≤ g x) : 0 ≤ erealIntegral μ g := by
  rw [erealIntegral_of_nonneg μ hg]; exact EReal.coe_ennreal_nonneg _

lemma erealIntegral_neg_le {E : Type*} [MeasurableSpace E] (μ : Measure E) {f g : E → EReal}
    (hg : ∀ x, 0 ≤ g x) (h : ∀ x, -g x ≤ f x) : -erealIntegral μ g ≤ erealIntegral μ f := by
  refine le_trans (le_of_eq ?_) (erealIntegral_mono μ h)
  rw [erealIntegral_of_nonneg μ hg]
  unfold erealIntegral
  have h1 : ∀ x, ((-g x) ⊔ 0).toENNReal = 0 := fun x => by
    rw [sup_of_le_right (by simpa using hg x)]; simp
  simp [h1]

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

lemma tail_policy (M : MarkovDecisionModel E A) {π : ℕ → E → A} (hπ : IsPolicyOf M π) :
    IsPolicyOf M (fun k => π (k + 1)) := fun k => hπ (k + 1)

lemma measurable_erealIntegral (M : MarkovDecisionModel E A) {f : E → A} (hf : Measurable f)
    {v : E → EReal} (hv : Measurable v) :
    Measurable (fun x => erealIntegral (M.Q (x, f x)) v) := by
  unfold erealIntegral
  have hm : Measurable (fun x : E => (x, f x)) := measurable_id.prodMk hf
  have k1 : Measurable (fun x => ∫⁻ y, (v y ⊔ 0).toENNReal ∂(M.Q (x, f x))) := by
    have := (Measurable.lintegral_kernel (κ := M.Q)
      (f := fun y => (v y ⊔ 0).toENNReal) (by fun_prop))
    exact this.comp hm
  have k2 : Measurable (fun x => ∫⁻ y, ((-v y) ⊔ 0).toENNReal ∂(M.Q (x, f x))) := by
    have := (Measurable.lintegral_kernel (κ := M.Q)
      (f := fun y => ((-v y) ⊔ 0).toENNReal) (by fun_prop))
    exact this.comp hm
  exact (measurable_coe_ennreal_ereal.comp k1).add (measurable_coe_ennreal_ereal.comp k2).neg

lemma Jnpi_measurable (M : MarkovDecisionModel E A) {rew : E × A → ℝ} (hrew : Measurable rew) :
    ∀ (n : ℕ) (π : ℕ → E → A), IsPolicyOf M π → Measurable (Jnpi M rew π n) := by
  intro n
  induction n with
  | zero => intro π _; exact measurable_const
  | succ n ih =>
    intro π hπ
    have hf : Measurable (π 0) := (hπ 0).1
    have h1 : Measurable (fun x => (rew (x, π 0 x) : EReal)) :=
      measurable_coe_real_ereal.comp (hrew.comp (measurable_id.prodMk hf))
    have h2 := measurable_erealIntegral M hf (ih _ (tail_policy M hπ))
    have : Jnpi M rew π (n + 1) = fun x => (rew (x, π 0 x) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q (x, π 0 x)) (Jnpi M rew (fun k => π (k + 1)) n) := by
      funext x; rfl
    rw [this]
    exact h1.add (h2.const_mul _)

abbrev rneg (M : MarkovDecisionModel E A) : E × A → ℝ := fun p => max (-M.r p) 0

lemma Jneg_nonneg (M : MarkovDecisionModel E A) :
    ∀ (n : ℕ) (π : ℕ → E → A) (x : E), 0 ≤ Jnpi M (rneg M) π n x := by
  intro n
  induction n with
  | zero => intro π x; simp [Jnpi]
  | succ n ih =>
    intro π x
    show 0 ≤ ((rneg M (x, π 0 x) : ℝ) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q (x, π 0 x)) (Jnpi M (rneg M) (fun k => π (k + 1)) n)
    refine add_nonneg (by exact_mod_cast le_max_right _ _) ?_
    exact mul_nonneg (by exact_mod_cast M.hβ0.le) (erealIntegral_nonneg _ (ih _))

lemma Jneg_succ (M : MarkovDecisionModel E A) :
    ∀ (n : ℕ) (π : ℕ → E → A) (x : E), Jnpi M (rneg M) π n x ≤ Jnpi M (rneg M) π (n + 1) x := by
  intro n
  induction n with
  | zero => intro π x; exact Jneg_nonneg M 1 π x
  | succ n ih =>
    intro π x
    show ((rneg M (x, π 0 x) : ℝ) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q (x, π 0 x)) (Jnpi M (rneg M) (fun k => π (k + 1)) n) ≤
      ((rneg M (x, π 0 x) : ℝ) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q (x, π 0 x)) (Jnpi M (rneg M) (fun k => π (k + 1)) (n + 1))
    gcongr
    · exact_mod_cast M.hβ0.le
    · exact erealIntegral_mono _ (fun y => ih _ y)

lemma Jneg_le_eps (M : MarkovDecisionModel E A) {π : ℕ → E → A} (hπ : IsPolicyOf M π)
    (n : ℕ) (x : E) : Jnpi M (rneg M) π n x ≤ epsilon M x := by
  have hmono : Monotone (fun k => Jnpi M (rneg M) π k x) :=
    monotone_nat_of_le_succ (fun k => Jneg_succ M k π x)
  have h1 : Jnpi M (rneg M) π n x ≤ Jinfpi M (rneg M) π x := by
    unfold Jinfpi
    apply le_limsup_of_frequently_le
    · exact (eventually_ge_atTop n).frequently.mono (fun k hk => hmono hk)
    · isBoundedDefault
  unfold epsilon
  exact le_trans h1 (le_biSup (fun π => Jinfpi M (fun p => max (-M.r p) 0) π x) hπ)

lemma J_ge_neg (M : MarkovDecisionModel E A) :
    ∀ (n : ℕ) (π : ℕ → E → A) (x : E), -Jnpi M (rneg M) π n x ≤ Jnpi M M.r π n x := by
  intro n
  induction n with
  | zero => intro π x; simp [Jnpi]
  | succ n ih =>
    intro π x
    show -(((rneg M (x, π 0 x) : ℝ) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q (x, π 0 x)) (Jnpi M (rneg M) (fun k => π (k + 1)) n)) ≤
      ((M.r (x, π 0 x) : ℝ) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q (x, π 0 x)) (Jnpi M M.r (fun k => π (k + 1)) n)
    have hI := erealIntegral_neg_le (M.Q (x, π 0 x)) (Jneg_nonneg M n (fun k => π (k + 1))) (ih (fun k => π (k + 1)))
    rw [EReal.neg_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
      ← EReal.coe_neg, sub_eq_add_neg]
    apply add_le_add
    · exact_mod_cast (show -max (-M.r (x, π 0 x)) 0 ≤ M.r (x, π 0 x) by
        have := le_max_left (-M.r (x, π 0 x)) 0; linarith)
    · rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left hI (by exact_mod_cast M.hβ0.le)

lemma eps_nonneg (M : MarkovDecisionModel E A) (x : E) : 0 ≤ epsilon M x := by
  obtain ⟨f, hf, hfD⟩ := M.hD_graph
  have hπ : IsPolicyOf M (fun _ => f) := fun _ => ⟨hf, hfD⟩
  have := Jneg_le_eps M hπ 0 x
  simpa [Jnpi] using this

lemma Tcirc_nonneg (M : MarkovDecisionModel E A) {v : E → EReal} (hv : ∀ x, 0 ≤ v x) (x : E) :
    0 ≤ Tcirc M v x := by
  obtain ⟨f, _, hfD⟩ := M.hD_graph
  unfold Tcirc
  refine le_trans ?_ (le_biSup (fun a => (M.β : EReal) * erealIntegral (M.Q (x, a)) v)
    (show f x ∈ M.Dx x from hfD x))
  exact mul_nonneg (by exact_mod_cast M.hβ0.le) (erealIntegral_nonneg _ hv)

lemma iter_nonneg (M : MarkovDecisionModel E A) :
    ∀ (m : ℕ) (x : E), 0 ≤ (Tcirc M)^[m] (epsilon M) x := by
  intro m
  induction m with
  | zero => exact eps_nonneg M
  | succ m ih =>
    intro x
    rw [Function.iterate_succ_apply']
    exact Tcirc_nonneg M ih x

lemma toENNReal_coe_sup (t : ℝ) : ((t : EReal) ⊔ 0).toENNReal = ENNReal.ofReal t := by
  rcases le_total t 0 with h | h
  · rw [sup_of_le_right (by exact_mod_cast h)]; simp [ENNReal.ofReal_of_nonpos h]
  · rw [sup_of_le_left (by exact_mod_cast h), EReal.toENNReal_of_ne_top (EReal.coe_ne_top t)]
    simp

lemma real_pw (a b t : ℝ) (h : a ≤ b + t) (ht : 0 ≤ t) :
    ENNReal.ofReal a + ENNReal.ofReal (-b) ≤
      ENNReal.ofReal b + ENNReal.ofReal (-a) + ENNReal.ofReal t := by
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness)
    (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_ofReal']
  have e1 := max_zero_sub_max_neg_zero_eq_self a
  have e2 := max_zero_sub_max_neg_zero_eq_self b
  have : max t 0 = t := max_eq_left ht
  linarith

lemma pw_bound {a b g : EReal} (hg : 0 ≤ g) (h : a - g ≤ b) :
    (a ⊔ 0).toENNReal + ((-b) ⊔ 0).toENNReal ≤
      (b ⊔ 0).toENNReal + ((-a) ⊔ 0).toENNReal + (g ⊔ 0).toENNReal := by
  rw [sup_of_le_left hg]
  induction g using EReal.rec with
  | bot => exact absurd hg (by simp)
  | top => simp
  | coe t =>
    have h1 : a ≤ b + t := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).1 h
    have ht : (0 : EReal) ≤ t := hg
    have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht
    induction a using EReal.rec with
    | bot => simp
    | top =>
      induction b using EReal.rec with
      | bot => simp at h1
      | top => simp
      | coe b => exact absurd h1 (by rw [top_le_iff, ← EReal.coe_add]; exact EReal.coe_ne_top _)
    | coe a =>
      induction b using EReal.rec with
      | bot => simp at h1
      | top => simp
      | coe b =>
        rw [← EReal.coe_neg, ← EReal.coe_neg, toENNReal_coe_sup, toENNReal_coe_sup,
          toENNReal_coe_sup, toENNReal_coe_sup, EReal.toENNReal_of_ne_top (EReal.coe_ne_top t)]
        have : ENNReal.ofReal (EReal.toReal (t : EReal)) = ENNReal.ofReal t := by simp
        rw [this]
        exact real_pw a b t (by rw [← EReal.coe_add] at h1; exact_mod_cast h1) ht'

lemma pw_bound2 {a b g : EReal} (hg : 0 ≤ g) (h : a - g ≤ b) :
    ((-b) ⊔ 0).toENNReal ≤ ((-a) ⊔ 0).toENNReal + (g ⊔ 0).toENNReal := by
  rw [sup_of_le_left hg]
  induction g using EReal.rec with
  | bot => exact absurd hg (by simp)
  | top => simp
  | coe t =>
    have h1 : a ≤ b + t := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).1 h
    have ht : (0 : EReal) ≤ t := hg
    refine le_trans (EReal.toENNReal_le_toENNReal ?_) EReal.toENNReal_add_le
    have h2 : -b ≤ -a + t := by
      rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
        ← EReal.neg_add (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _))]
      exact EReal.neg_le_neg_iff.2 h1
    refine sup_le (le_trans h2 ?_) ?_
    · exact add_le_add le_sup_left le_rfl
    · exact le_trans (le_add_of_nonneg_right ht) (add_le_add le_sup_right le_rfl)

lemma arith (Pm Nm Pn Nn S : ENNReal) (h1 : Pm + Nn ≤ Pn + Nm + S) (h2 : Nn ≤ Nm + S) :
    ((Pm : EReal) + -(Nm : EReal)) - (S : EReal) ≤ (Pn : EReal) + -(Nn : EReal) := by
  rcases eq_or_ne S ⊤ with hS | hS
  · simp [hS]
  rcases eq_or_ne Nm ⊤ with hNm | hNm
  · simp [hNm]
  have hNn : Nn ≠ ⊤ := (lt_of_le_of_lt h2 (ENNReal.add_lt_top.2 ⟨hNm.lt_top, hS.lt_top⟩)).ne
  rcases eq_or_ne Pn ⊤ with hPn | hPn
  · have : (Nn : EReal) ≠ ⊤ := by simpa using hNn
    rw [hPn, EReal.coe_ennreal_top, EReal.top_add_of_ne_bot (by simpa using this)]
    exact le_top
  have hPm : Pm ≠ ⊤ := by
    have := lt_of_le_of_lt h1 (by finiteness : Pn + Nm + S < ⊤)
    exact (lt_of_le_of_lt le_self_add this).ne
  have e1 := ENNReal.toReal_mono (by finiteness) h1
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness)
    (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness)] at e1
  rw [← EReal.coe_ennreal_toReal hS, ← EReal.coe_ennreal_toReal hNm, ← EReal.coe_ennreal_toReal hPn,
    ← EReal.coe_ennreal_toReal hNn, ← EReal.coe_ennreal_toReal hPm]
  rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_sub,
    EReal.coe_le_coe_iff]
  linarith

lemma int_bound {μ : Measure E} {a b g : E → EReal} (ha : Measurable a) (hb : Measurable b)
    (hg : ∀ y, 0 ≤ g y) (h : ∀ y, a y - g y ≤ b y) :
    erealIntegral μ a - erealIntegral μ g ≤ erealIntegral μ b := by
  rw [erealIntegral_of_nonneg μ hg]
  unfold erealIntegral
  apply arith
  · rw [← lintegral_add_left (by fun_prop), ← lintegral_add_left (by fun_prop),
      ← lintegral_add_left (by fun_prop)]
    exact lintegral_mono fun y => pw_bound (hg y) (h y)
  · rw [← lintegral_add_left (by fun_prop)]
    exact lintegral_mono fun y => pw_bound2 (hg y) (h y)

lemma partA (M : MarkovDecisionModel E A) :
    ∀ (m n : ℕ) (π : ℕ → E → A) (x : E), IsPolicyOf M π → m ≤ n →
      Jnpi M M.r π m x - (Tcirc M)^[m] (epsilon M) x ≤ Jnpi M M.r π n x := by
  intro m
  induction m with
  | zero =>
    intro n π x hπ _
    simp only [Function.iterate_zero, id, Jnpi, zero_sub]
    exact le_trans (EReal.neg_le_neg_iff.2 (Jneg_le_eps M hπ n x)) (J_ge_neg M n π x)
  | succ m ih =>
    intro n π x hπ hmn
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Function.iterate_succ_apply']
    set G := (Tcirc M)^[m] (epsilon M) with hG
    have hG0 : ∀ y, 0 ≤ G y := iter_nonneg M m
    have hπ' := tail_policy M hπ
    have hT : (M.β : EReal) * erealIntegral (M.Q (x, π 0 x)) G ≤ Tcirc M G x := by
      unfold Tcirc
      exact le_biSup (fun a => (M.β : EReal) * erealIntegral (M.Q (x, a)) G)
        (show π 0 x ∈ M.Dx x from (hπ 0).2 x)
    have hkey := int_bound (μ := M.Q (x, π 0 x))
      (Jnpi_measurable M M.hr_meas m _ hπ') (Jnpi_measurable M M.hr_meas n _ hπ') hG0
      (fun y => ih n (fun k => π (k + 1)) y hπ' (by omega))
    have hβ : (0 : EReal) ≤ M.β := by exact_mod_cast M.hβ0.le
    show ((M.r (x, π 0 x) : ℝ) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q (x, π 0 x)) (Jnpi M M.r (fun k => π (k + 1)) m) - Tcirc M G x ≤
      ((M.r (x, π 0 x) : ℝ) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q (x, π 0 x)) (Jnpi M M.r (fun k => π (k + 1)) n)
    calc _ ≤ ((M.r (x, π 0 x) : ℝ) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q (x, π 0 x)) (Jnpi M M.r (fun k => π (k + 1)) m) -
          (M.β : EReal) * erealIntegral (M.Q (x, π 0 x)) G := EReal.sub_le_sub le_rfl hT
      _ = ((M.r (x, π 0 x) : ℝ) : EReal) + (M.β : EReal) *
          (erealIntegral (M.Q (x, π 0 x)) (Jnpi M M.r (fun k => π (k + 1)) m) -
            erealIntegral (M.Q (x, π 0 x)) G) := by
        rw [EReal.mul_sub_of_nonneg_of_ne_top hβ (EReal.coe_ne_top _), sub_eq_add_neg,
          sub_eq_add_neg, add_assoc]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hkey hβ)

lemma sup_sub_le {ι : Type*} (P : Set ι) (F H : ι → EReal) {c : EReal} (hc : 0 ≤ c)
    (h : ∀ i ∈ P, F i - c ≤ H i) : (⨆ i ∈ P, F i) - c ≤ ⨆ i ∈ P, H i := by
  induction c using EReal.rec with
  | bot => exact absurd hc (by simp)
  | top => simp
  | coe t =>
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine iSup₂_le fun i hi => ?_
    have := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).1 (h i hi)
    exact le_trans this (add_le_add (le_biSup H hi) le_rfl)

end L741Aux

open L741Aux in
theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (hAneg : IntegrabilityAssumptionAneg M)
    (π : ℕ → E → A) (hπ : IsPolicyOf M π) (n m : ℕ) (hnm : m ≤ n) (x : E) :
    (Jnpi M M.r π m x - (Tcirc M)^[m] (epsilon M) x ≤ Jnpi M M.r π n x ∧
        Jn M M.r m x - (Tcirc M)^[m] (epsilon M) x ≤ Jn M M.r n x) ∧
      (∀ x', -epsilon M x' ≤ Jinfpi M M.r π x') := by
  refine ⟨⟨partA M m n π x hπ hnm, ?_⟩, ?_⟩
  · unfold Jn
    exact sup_sub_le _ _ _ (iter_nonneg M m x) (fun σ hσ => partA M m n σ x hσ hnm)
  · intro x'
    unfold Jinfpi
    apply le_limsup_of_frequently_le
    · exact Frequently.of_forall fun k =>
        le_trans (EReal.neg_le_neg_iff.2 (Jneg_le_eps M hπ k x')) (J_ge_neg M k π x')
    · isBoundedDefault
