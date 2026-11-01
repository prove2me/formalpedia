-- Prove2me | solution 1 for KellyLossNetworks.Routing.theorem_4_45
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T18:03:37.995756+00:00
-- url     : https://prove2.me/submissions/1ce329c5-9488-4798-baaa-e84f110ccb63

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

namespace KellyLossNetworks.Routing.Aux
open KellyLossNetworks.Routing

/-- Chernoff bound for i.i.d. sums with exponential decay rate. -/
theorem chernoff_iid {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (W : α → ℝ) (hW : Measurable W) (B : ℝ) (hB : ∀ a, -B ≤ W a) (c : ℝ)
    (hmean : ∫ a, W a ∂ν < c) (t : ℝ) (ht : 0 < t)
    (hexp : Integrable (fun a => Real.exp (t * W a)) ν) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ (S : Type) [Fintype S],
      (Measure.pi (fun _ : S => ν)).real {w | c * (Fintype.card S : ℝ) ≤ ∑ i, W (w i)} ≤
        r ^ Fintype.card S := by
  -- integrability for nonpositive exponents
  have hneg : ∀ s : ℝ, s ≤ 0 → Integrable (fun a => Real.exp (s * W a)) ν := by
    intro s hs
    refine Integrable.mono' (integrable_const (Real.exp (-s * B))) ?_ (ae_of_all _ fun a => ?_)
    · exact (Real.measurable_exp.comp (hW.const_mul s)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have := hB a
      nlinarith
  have hint : ∀ s : ℝ, s ≤ t → Integrable (fun a => Real.exp (s * W a)) ν := by
    intro s hs
    rcases le_or_gt s 0 with h0 | h0
    · exact hneg s h0
    · exact integrable_exp_mul_of_le_of_le (hneg 0 le_rfl) hexp h0.le hs
  have h0int : (0 : ℝ) ∈ interior (integrableExpSet W ν) := by
    rw [mem_interior_iff_mem_nhds]
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact hint s (le_of_lt hs)
  set f : ℝ → ℝ := fun s => Real.exp (-(s * c)) * mgf W ν s with hf
  have hd : HasDerivAt f (-c + ∫ a, W a ∂ν) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-(s * c))) (Real.exp (-(0 * c)) * (-(1 * c))) 0 :=
      ((hasDerivAt_id (0:ℝ)).mul_const c).neg.exp
    have h2 := hasDerivAt_mgf h0int
    have h3 := h1.mul h2
    have e : (-c + ∫ a, W a ∂ν) = (Real.exp (-(0 * c)) * (-(1 * c))) * mgf W ν 0 +
        Real.exp (-(0 * c)) * ∫ a, W a * Real.exp (0 * W a) ∂ν := by
      simp [mgf_zero]
    rw [e]
    exact h3
  have hslope := hd.tendsto_slope_zero_right
  have hlt : -c + ∫ a, W a ∂ν < 0 := by linarith
  have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), s⁻¹ • (f (0 + s) - f 0) < 0 :=
    hslope.eventually (Iio_mem_nhds hlt)
  have hev2 : ∀ᶠ s in 𝓝[>] (0:ℝ), s ∈ Set.Ioo 0 t :=
    Ioo_mem_nhdsGT ht
  obtain ⟨s, hs1, hs2⟩ := (hev.and hev2).exists
  have hf0 : f 0 = 1 := by simp [hf]
  have hfs : f s < 1 := by
    rw [zero_add, hf0, smul_eq_mul] at hs1
    have hspos : 0 < s := hs2.1
    have : s⁻¹ * (f s - 1) < 0 := hs1
    have h' : f s - 1 < 0 := by
      by_contra hcon
      push Not at hcon
      have : 0 ≤ s⁻¹ * (f s - 1) := mul_nonneg (inv_nonneg.mpr hspos.le) hcon
      linarith
    linarith
  refine ⟨f s, mul_nonneg (Real.exp_pos _).le mgf_nonneg, hfs, ?_⟩
  intro S _
  set P := Measure.pi (fun _ : S => ν)
  have hspos : 0 < s := hs2.1
  have hindep : iIndepFun (fun i (w : S → α) => W (w i)) P :=
    iIndepFun_pi (fun _ => hW.aemeasurable)
  have hmeas : ∀ i : S, Measurable (fun w : S → α => W (w i)) :=
    fun i => hW.comp (measurable_pi_apply i)
  have hsum : (fun w : S → α => ∑ i, W (w i)) = ∑ i ∈ Finset.univ, (fun w : S → α => W (w i)) := by
    ext w; simp
  have hmgf_i : ∀ i : S, mgf (fun w : S → α => W (w i)) P s = mgf W ν s := by
    intro i
    simp only [mgf]
    exact integral_comp_eval (μ := fun _ : S => ν) (i := i) (f := fun a => Real.exp (s * W a))
      ((Real.measurable_exp.comp (hW.const_mul s)).aestronglyMeasurable)
  have hint_i : ∀ i ∈ (Finset.univ : Finset S),
      Integrable (fun w : S → α => Real.exp (s * W (w i))) P := by
    intro i _
    exact (integrable_comp_eval (μ := fun _ : S => ν) (i := i) (hint s hs2.2.le))
  have hintS := hindep.integrable_exp_mul_sum (t := s) hmeas hint_i
  have hch := measure_ge_le_exp_mul_mgf (μ := P) (X := fun w : S → α => ∑ i, W (w i))
    (c * (Fintype.card S : ℝ)) hspos.le (by simpa [Finset.sum_apply] using hintS)
  have hm : mgf (fun w : S → α => ∑ i, W (w i)) P s = (mgf W ν s) ^ Fintype.card S := by
    rw [hsum, hindep.mgf_sum hmeas]
    simp [hmgf_i]
  calc P.real {w | c * (Fintype.card S : ℝ) ≤ ∑ i, W (w i)}
      ≤ Real.exp (-s * (c * (Fintype.card S : ℝ))) * mgf (fun w : S → α => ∑ i, W (w i)) P s := hch
    _ = f s ^ Fintype.card S := by
      rw [hm, hf]
      simp only
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring


theorem card_ge_three_of_not_mem {K : ℕ} (e : Edge K) (k : Fin K) (hk : k ∉ e.1) : 3 ≤ K := by
  classical
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using he
    have hk' : k ≠ a ∧ k ≠ b := by simpa [Sym2.mem_iff, not_or] using hk
    have h3 : ({a, b, k} : Finset (Fin K)).card = 3 :=
      Finset.card_eq_three.mpr ⟨a, b, k, hab, hk'.1.symm, hk'.2.symm, rfl⟩
    have := Finset.card_le_univ ({a, b, k} : Finset (Fin K))
    simpa [h3] using this

theorem reserve_nonneg {K : ℕ} (C D : ℝ) (hD : 0 < D) (x : Edge K → ℝ) (e : Edge K)
    (k : Fin K) : 0 ≤ reserve C D x e k := by
  unfold reserve
  split_ifs with hk
  · exact le_rfl
  · have h3 := card_ge_three_of_not_mem e k hk
    have hK : (0 : ℝ) < (K : ℝ) - 2 := by
      have : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast h3
      linarith
    apply div_nonneg
    · exact mul_nonneg (le_max_right _ _) (Finset.prod_nonneg fun g _ => le_max_right _ _)
    · exact (mul_pos hK hD).le

theorem detourLoad_mono {K : ℕ} (f f' : Edge K → Fin K → ℝ) (h : ∀ e k, f e k ≤ f' e k)
    (g : Edge K) : detourLoad f g ≤ detourLoad f' g := by
  unfold detourLoad
  apply Finset.sum_le_sum; intro e _
  apply Finset.sum_le_sum; intro k _
  split_ifs
  · exact h e k
  · exact le_rfl

/-- Deterministic core of Kelly's proof of Theorem 4.45: if the reservation covers every
overload and no edge is over-reserved, the loads are routable. -/
theorem feasible_of_reserve {K : ℕ} (C D : ℝ) (hC : 0 < C) (hD : 0 < D) (x : Edge K → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hA : ∀ e, max (x e - C) 0 ≤ ∑ k, reserve C D x e k)
    (hB : ∀ g, detourLoad (reserve C D x) g ≤ max (C - x g) 0) : Feasible C x := by
  set r := reserve C D x with hr
  set S : Edge K → ℝ := fun e => ∑ k, r e k with hS
  set m : Edge K → ℝ := fun e => max (x e - C) 0 with hm
  have hr0 : ∀ e k, 0 ≤ r e k := fun e k => reserve_nonneg C D hD x e k
  have hS0 : ∀ e, 0 ≤ S e := fun e => Finset.sum_nonneg fun k _ => hr0 e k
  have hm0 : ∀ e, 0 ≤ m e := fun e => le_max_right _ _
  have hmS : ∀ e, m e ≤ S e := hA
  have hq0 : ∀ e, 0 ≤ m e / S e := fun e => div_nonneg (hm0 e) (hS0 e)
  have hq1 : ∀ e, m e / S e ≤ 1 := by
    intro e
    rcases (hS0 e).eq_or_lt with h | h
    · rw [← h, div_zero]; exact zero_le_one
    · exact (div_le_one h).mpr (hmS e)
  refine ⟨fun e k => r e k * (m e / S e), ?_, ?_, ?_, ?_⟩
  · intro e k; exact mul_nonneg (hr0 e k) (hq0 e)
  · intro e k hk
    simp only [hr, reserve, if_pos hk, zero_mul]
  · -- the total two-edge flow is exactly the overload `m e`
    have hsum : ∀ e, ∑ k, r e k * (m e / S e) = m e := by
      intro e
      rw [← Finset.sum_mul]
      change S e * (m e / S e) = m e
      rcases (hS0 e).eq_or_lt with h | h
      · have : m e = 0 := le_antisymm (h ▸ hmS e) (hm0 e)
        rw [this, zero_div, mul_zero]
      · field_simp
    intro e
    rw [hsum e]
    simp only [hm]
    exact max_le (by linarith [hx e]) (hx e)
  · intro g
    have hsum : ∑ k, r g k * (m g / S g) = m g := by
      rw [← Finset.sum_mul]
      change S g * (m g / S g) = m g
      rcases (hS0 g).eq_or_lt with h | h
      · have : m g = 0 := le_antisymm (h ▸ hmS g) (hm0 g)
        rw [this, zero_div, mul_zero]
      · field_simp
    have hdl : detourLoad (fun e k => r e k * (m e / S e)) g ≤ detourLoad r g :=
      detourLoad_mono _ _ (fun e k => by
        have := mul_le_mul_of_nonneg_left (hq1 e) (hr0 e k)
        simpa using this) g
    rw [hsum]
    have hBg := hB g
    rcases le_total (x g) C with h | h
    · have h1 : m g = 0 := max_eq_right (by linarith)
      have h2 : max (C - x g) 0 = C - x g := max_eq_left (by linarith)
      rw [h1]; rw [h2] at hBg; linarith
    · have h1 : m g = x g - C := max_eq_left (by linarith)
      have h2 : max (C - x g) 0 = 0 := max_eq_right (by linarith)
      rw [h1]; rw [h2] at hBg; linarith


/-- The edge `{a, b}` of the complete graph. -/
def E {K : ℕ} (a b : Fin K) (h : a ≠ b) : Edge K := ⟨s(a, b), by simpa using h⟩

theorem E_swap {K : ℕ} (a b : Fin K) (h : a ≠ b) : E a b h = E b a h.symm :=
  Subtype.ext Sym2.eq_swap

/-- The tandem nodes of the pair `{a, b}`. -/
abbrev T {K : ℕ} (a b : Fin K) : Type := {k : Fin K // k ≠ a ∧ k ≠ b}

open Classical in
theorem filter_onDetour {K : ℕ} (a b k : Fin K) (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) :
    Finset.univ.filter (OnDetour (E a b hab) k) = {E a k hka.symm, E b k hkb.symm} := by
  apply Finset.ext
  intro g
  rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  simp only [Finset.mem_univ, true_and, OnDetour, E, Subtype.ext_iff, Sym2.mem_iff]
  constructor
  · rintro ⟨_, v, hv, hg⟩
    rcases hv with rfl | rfl
    · exact Or.inl hg
    · exact Or.inr hg
  · rintro (hg | hg)
    · exact ⟨by tauto, a, Or.inl rfl, hg⟩
    · exact ⟨by tauto, b, Or.inr rfl, hg⟩

theorem reserve_E {K : ℕ} (C D : ℝ) (x : Edge K → ℝ) (a b k : Fin K) (hab : a ≠ b)
    (hka : k ≠ a) (hkb : k ≠ b) :
    reserve C D x (E a b hab) k = max (x (E a b hab) - C) 0 *
      (max (C - x (E a k hka.symm)) 0 * max (C - x (E b k hkb.symm)) 0) /
      (((K : ℝ) - 2) * D) := by
  classical
  have hk : k ∉ (E a b hab).1 := by
    simp only [E, Sym2.mem_iff, not_or]; exact ⟨hka, hkb⟩
  have hne : E a k hka.symm ≠ E b k hkb.symm := by
    intro h
    have := congrArg Subtype.val h
    simp only [E] at this
    exact hab (Sym2.congr_left.mp this)
  unfold reserve
  rw [if_neg hk]
  congr 2
  convert Finset.prod_pair (f := fun g => max (C - x g) 0) hne using 2
  exact filter_onDetour a b k hab hka hkb

theorem reserve_mem {K : ℕ} (C D : ℝ) (x : Edge K → ℝ) (e : Edge K) (k : Fin K)
    (hk : k ∈ e.1) : reserve C D x e k = 0 := by
  unfold reserve; rw [if_pos hk]

/-- Sum of the reservations of the pair `{a, b}` over its tandem nodes. -/
theorem sum_reserve_E {K : ℕ} (C D : ℝ) (x : Edge K → ℝ) (a b : Fin K) (hab : a ≠ b) :
    ∑ k, reserve C D x (E a b hab) k = max (x (E a b hab) - C) 0 / (((K : ℝ) - 2) * D) *
      ∑ k : T a b, max (C - x (E a k.1 k.2.1.symm)) 0 * max (C - x (E b k.1 k.2.2.symm)) 0 := by
  classical
  rw [Finset.mul_sum]
  have h1 : ∑ k, reserve C D x (E a b hab) k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ a ∧ k ≠ b), reserve C D x (E a b hab) k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with h
    · rfl
    · apply reserve_mem
      simp only [E, Sym2.mem_iff]
      tauto
  rw [h1, Finset.sum_subtype (Finset.univ.filter (fun k : Fin K => k ≠ a ∧ k ≠ b))
    (p := fun k : Fin K => k ≠ a ∧ k ≠ b) (by simp)]
  apply Finset.sum_congr rfl
  intro k _
  rw [reserve_E C D x a b k.1 hab k.2.1 k.2.2]
  ring

/-- Edges through `a` avoiding `k` are the edges `{a, b}`, `b` a tandem node of `{a, k}`. -/
theorem sum_edges_through {K : ℕ} (a k : Fin K) (hak : a ≠ k) (F : Edge K → ℝ) :
    ∑ e, (if k ∉ e.1 ∧ a ∈ e.1 then F e else 0) =
      ∑ b : T a k, F (E a b.1 b.2.1.symm) := by
  classical
  rw [← Finset.sum_filter]
  have hinj : Function.Injective (fun b : T a k => E a b.1 b.2.1.symm) := by
    intro b b' h
    have := congrArg Subtype.val h
    simp only [E] at this
    exact Subtype.ext (Sym2.congr_right.mp this)
  rw [show (∑ b : T a k, F (E a b.1 b.2.1.symm)) =
      ∑ e ∈ Finset.univ.map ⟨_, hinj⟩, F e from
      (Finset.sum_map Finset.univ ⟨fun b : T a k => E a b.1 b.2.1.symm, hinj⟩ F).symm]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hk, ha⟩
    obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp ha
    have hya : y ≠ a := by
      intro h; apply e.2; rw [hy, h]; simp
    have hyk : y ≠ k := by
      intro h; apply hk; rw [hy, h]; simp
    exact ⟨⟨y, hya, hyk⟩, Subtype.ext (by simp [E, hy])⟩
  · rintro ⟨b, rfl⟩
    have h1 : k ≠ a := hak.symm
    have h2 : k ≠ b.1 := b.2.2.symm
    simp only [E, Sym2.mem_iff, not_or]
    tauto

theorem onDetour_E_iff {K : ℕ} (a k : Fin K) (hak : a ≠ k) (e : Edge K) :
    OnDetour e k (E a k hak) ↔ (k ∉ e.1 ∧ a ∈ e.1) := by
  simp only [OnDetour, E]
  constructor
  · rintro ⟨hk, v, hv, h⟩
    exact ⟨hk, (Sym2.congr_left.mp h) ▸ hv⟩
  · rintro ⟨hk, ha⟩
    exact ⟨hk, a, ha, rfl⟩

/-- The two-edge load reserved through the edge `{a, k}`. -/
theorem detourLoad_reserve_E {K : ℕ} (C D : ℝ) (x : Edge K → ℝ) (a k : Fin K) (hak : a ≠ k) :
    detourLoad (reserve C D x) (E a k hak) =
      max (C - x (E a k hak)) 0 / (((K : ℝ) - 2) * D) *
      ∑ b : T a k, (max (x (E a b.1 b.2.1.symm) - C) 0 * max (C - x (E k b.1 b.2.2.symm)) 0 +
        max (x (E k b.1 b.2.2.symm) - C) 0 * max (C - x (E a b.1 b.2.1.symm)) 0) := by
  classical
  unfold detourLoad
  rw [Finset.sum_comm]
  rw [Fintype.sum_eq_add k a hak.symm]
  · -- tandem node `k` (pairs `{a, b}`) and tandem node `a` (pairs `{k, b}`)
    have hk : ∀ e : Edge K, (if OnDetour e k (E a k hak) then reserve C D x e k else 0) =
        (if k ∉ e.1 ∧ a ∈ e.1 then reserve C D x e k else 0) := by
      intro e; simp only [onDetour_E_iff]
    have ha : ∀ e : Edge K, (if OnDetour e a (E a k hak) then reserve C D x e a else 0) =
        (if a ∉ e.1 ∧ k ∈ e.1 then reserve C D x e a else 0) := by
      intro e; rw [E_swap a k hak]; simp only [onDetour_E_iff]
    simp only [hk, ha]
    rw [sum_edges_through a k hak, sum_edges_through k a hak.symm]
    have hT : ∀ (G : T k a → ℝ), ∑ b : T k a, G b =
        ∑ b : T a k, G ⟨b.1, b.2.2, b.2.1⟩ := by
      intro G
      exact Fintype.sum_equiv ⟨fun b => ⟨b.1, b.2.2, b.2.1⟩, fun b => ⟨b.1, b.2.2, b.2.1⟩,
        fun _ => rfl, fun _ => rfl⟩ _ _ (fun _ => rfl)
    rw [hT, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [reserve_E C D x a b.1 k b.2.1.symm hak.symm b.2.2.symm,
      reserve_E C D x k b.1 a b.2.2.symm hak b.2.1.symm]
    rw [E_swap b.1 k b.2.2, E_swap k a hak.symm, E_swap b.1 a b.2.1]
    ring
  · intro c hc
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg]
    rintro ⟨_, v, _, h⟩
    have : c ∈ (E a k hak).1 := by rw [h]; simp
    simp only [E, Sym2.mem_iff] at this
    tauto

theorem mp_comp_injective {I J : Type} [Fintype I] [Fintype J] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (σ : J → I) (hσ : Function.Injective σ) :
    MeasurePreserving (fun (x : I → ℝ) (j : J) => x (σ j))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  classical
  let p : I → Prop := fun i => i ∈ Set.range σ
  letI : Fintype (Subtype p) := Subtype.fintype p
  have h1 := measurePreserving_piEquivPiSubtypeProd (α := fun _ : I => ℝ) (fun _ : I => μ) p
  have h2 : MeasurePreserving (Prod.fst : ((Subtype p → ℝ) × ({i // ¬ p i} → ℝ)) → (Subtype p → ℝ))
      ((Measure.pi fun _ : Subtype p => μ).prod (Measure.pi fun _ : {i // ¬ p i} => μ))
      (Measure.pi fun _ : Subtype p => μ) :=
    ⟨measurable_fst, by rw [Measure.map_fst_prod]; simp⟩
  let eqv : J ≃ Subtype p := Equiv.ofInjective σ hσ
  have h3 := measurePreserving_piCongrLeft (α := fun _ : J => ℝ) (fun _ : J => μ) eqv.symm
  have h4 := h3.comp (h2.comp h1)
  convert h4 using 1
  ext x j
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, eqv, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, p]

/-- The pair map: for each tandem node `k` of `{a, b}`, the loads of the two edges of the route. -/
def pairMap {K : ℕ} (a b : Fin K) (x : Edge K → ℝ) : T a b → ℝ × ℝ :=
  fun k => (x (E a k.1 k.2.1.symm), x (E b k.1 k.2.2.symm))

theorem pairMap_mp {K : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : Fin K) (hab : a ≠ b) :
    MeasurePreserving (pairMap a b) (Measure.pi fun _ : Edge K => μ)
      (Measure.pi fun _ : T a b => μ.prod μ) := by
  classical
  let σ : T a b ⊕ T a b → Edge K :=
    Sum.elim (fun k => E a k.1 k.2.1.symm) (fun k => E b k.1 k.2.2.symm)
  have hσ : Function.Injective σ := by
    rintro (k | k) (k' | k') h <;>
      simp only [σ, Sum.elim_inl, Sum.elim_inr, E, Subtype.ext_iff, Sym2.eq_iff] at h
    · simp only [Sum.inl.injEq]; apply Subtype.ext; rcases h with h | h
      · exact h.2
      · exact absurd h.2 k.2.1
    · rcases h with h | h
      · exact absurd h.1 hab
      · exact absurd h.2 k.2.2
    · rcases h with h | h
      · exact absurd h.1.symm hab
      · exact absurd h.2 k.2.1
    · simp only [Sum.inr.injEq]; apply Subtype.ext; rcases h with h | h
      · exact h.2
      · exact absurd h.2 k.2.2
  have h1 := mp_comp_injective μ σ hσ
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : T a b ⊕ T a b => ℝ)
    (fun _ => μ)
  have h3 := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (T a b)
    (fun _ => μ) (fun _ => μ)).symm
  have h4 := h3.comp (h2.comp h1)
  convert h4 using 1
  ext x k <;> rfl


theorem card_T {K : ℕ} (a b : Fin K) (hab : a ≠ b) : Fintype.card (T a b) = K - 2 := by
  classical
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter (fun k : Fin K => k ≠ a ∧ k ≠ b)) = (Finset.univ \ {a, b}) := by
    ext k; simp [not_or]
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_pair hab]

theorem tendsto_sq_mul_pow_sub_two (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun K : ℕ => (K : ℝ) ^ 2 * r ^ (K - 2)) atTop (𝓝 0) := by
  set q : ℝ := max r (1 / 2) with hq
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq1 : q < 1 := max_lt hr1 (by norm_num)
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 (abs_lt.mpr ⟨by linarith, hq1⟩)).div_const
    (q ^ 2)
  rw [zero_div] at h
  refine squeeze_zero' (Eventually.of_forall fun K => by positivity) ?_ h
  filter_upwards [eventually_ge_atTop 2] with K hK
  have h1 : r ^ (K - 2) ≤ q ^ (K - 2) := pow_le_pow_left₀ hr0 (le_max_left _ _) _
  have h2 : q ^ K = q ^ (K - 2) * q ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hK]
  rw [h2, mul_div_assoc, mul_div_cancel_right₀ _ (by positivity)]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem exists_E {K : ℕ} (e : Edge K) : ∃ a b : Fin K, ∃ h : a ≠ b, e = E a b h := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b => exact ⟨a, b, by simpa using he, rfl⟩

/-- The clamped spare capacity `min ((C - t)⁺, C)`. -/
noncomputable def gC (C t : ℝ) : ℝ := min (max (C - t) 0) C

/-- Clamped version of `Y` (unscaled). -/
noncomputable def Yc (C : ℝ) (p : ℝ × ℝ) : ℝ := gC C p.1 * gC C p.2

/-- Clamped version of `Z` (unscaled). -/
noncomputable def Zc (C : ℝ) (p : ℝ × ℝ) : ℝ :=
  max (p.1 - C) 0 * gC C p.2 + max (p.2 - C) 0 * gC C p.1

theorem gC_nonneg {C : ℝ} (hC : 0 ≤ C) (t : ℝ) : 0 ≤ gC C t := le_min (le_max_right _ _) hC

theorem gC_le (C t : ℝ) : gC C t ≤ C := min_le_right _ _

theorem gC_of_nonneg {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) : gC C t = max (C - t) 0 :=
  min_eq_left (max_le (by linarith) hC)

theorem measurable_gC (C : ℝ) : Measurable (gC C) :=
  ((measurable_const.sub measurable_id).max measurable_const).min measurable_const

theorem measurable_Yc (C : ℝ) : Measurable (Yc C) :=
  ((measurable_gC C).comp measurable_fst).mul ((measurable_gC C).comp measurable_snd)

theorem measurable_Zc (C : ℝ) : Measurable (Zc C) :=
  (((measurable_fst.sub_const C).max measurable_const).mul
      ((measurable_gC C).comp measurable_snd)).add
    (((measurable_snd.sub_const C).max measurable_const).mul
      ((measurable_gC C).comp measurable_fst))

theorem Yc_nonneg {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : 0 ≤ Yc C p :=
  mul_nonneg (gC_nonneg hC _) (gC_nonneg hC _)

theorem Yc_le {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : Yc C p ≤ C ^ 2 := by
  unfold Yc
  rw [sq]
  exact mul_le_mul (gC_le _ _) (gC_le _ _) (gC_nonneg hC _) hC

theorem Zc_nonneg {C : ℝ} (hC : 0 ≤ C) (p : ℝ × ℝ) : 0 ≤ Zc C p :=
  add_nonneg (mul_nonneg (le_max_right _ _) (gC_nonneg hC _))
    (mul_nonneg (le_max_right _ _) (gC_nonneg hC _))

theorem good_feasible {K : ℕ} (C D : ℝ) (hC : 0 < C) (hD : 0 < D) (hK : 3 ≤ K)
    (x : Edge K → ℝ) (hx : ∀ g, 0 ≤ x g)
    (h1 : ∀ a b : Fin K, a ≠ b → ((K : ℝ) - 2) * D < ∑ k : T a b, Yc C (pairMap a b x k))
    (h2 : ∀ a b : Fin K, a ≠ b → ∑ k : T a b, Zc C (pairMap a b x k) ≤ ((K : ℝ) - 2) * D) :
    Feasible C x := by
  have hK2 : (0 : ℝ) < (K : ℝ) - 2 := by
    have : (3 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hpos : 0 < ((K : ℝ) - 2) * D := mul_pos hK2 hD
  have hg : ∀ g, gC C (x g) = max (C - x g) 0 := fun g => gC_of_nonneg hC.le (hx g)
  apply feasible_of_reserve C D hC hD x hx
  · intro e
    obtain ⟨a, b, hab, rfl⟩ := exists_E e
    rw [sum_reserve_E]
    have hsum : (∑ k : T a b, max (C - x (E a k.1 k.2.1.symm)) 0 *
        max (C - x (E b k.1 k.2.2.symm)) 0) = ∑ k : T a b, Yc C (pairMap a b x k) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [Yc, pairMap, hg]
    rw [hsum, div_mul_eq_mul_div, le_div_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left (h1 a b hab).le (le_max_right _ _)
  · intro g
    obtain ⟨a, k, hak, rfl⟩ := exists_E g
    rw [detourLoad_reserve_E]
    have hsum : (∑ b : T a k, (max (x (E a b.1 b.2.1.symm) - C) 0 *
        max (C - x (E k b.1 b.2.2.symm)) 0 + max (x (E k b.1 b.2.2.symm) - C) 0 *
        max (C - x (E a b.1 b.2.1.symm)) 0)) = ∑ b : T a k, Zc C (pairMap a k x b) := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [Zc, pairMap, hg]
    rw [hsum, div_mul_eq_mul_div, div_le_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left (h2 a k hak) (le_max_right _ _)

/-- Bad event for `Y` (Chernoff form, `W = -Y`, `c = -D`). -/
def A1 (C D : ℝ) (S : Type) [Fintype S] : Set (S → ℝ × ℝ) :=
  {w | -D * (Fintype.card S : ℝ) ≤ ∑ i, -Yc C (w i)}

/-- Bad event for `Z` (Chernoff form, `W = Z`, `c = D`). -/
def A2 (C D : ℝ) (S : Type) [Fintype S] : Set (S → ℝ × ℝ) :=
  {w | D * (Fintype.card S : ℝ) ≤ ∑ i, Zc C (w i)}

theorem measurableSet_A1 (C D : ℝ) (S : Type) [Fintype S] : MeasurableSet (A1 C D S) :=
  measurableSet_le measurable_const
    (Finset.measurable_sum _ fun i _ => (measurable_Yc C).neg.comp (measurable_pi_apply i))

theorem measurableSet_A2 (C D : ℝ) (S : Type) [Fintype S] : MeasurableSet (A2 C D S) :=
  measurableSet_le measurable_const
    (Finset.measurable_sum _ fun i _ => (measurable_Zc C).comp (measurable_pi_apply i))

theorem prob_bad (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t)
    (C D : ℝ) (hC : 0 < C) (hD : 0 < D) (r1 r2 : ℝ) (hr10 : 0 ≤ r1) (hr20 : 0 ≤ r2)
    (hr1 : ∀ (S : Type) [Fintype S],
      (Measure.pi fun _ : S => μ.prod μ).real (A1 C D S) ≤ r1 ^ Fintype.card S)
    (hr2 : ∀ (S : Type) [Fintype S],
      (Measure.pi fun _ : S => μ.prod μ).real (A2 C D S) ≤ r2 ^ Fintype.card S)
    (K : ℕ) (hK : 3 ≤ K) :
    1 - ENNReal.ofReal ((K : ℝ) ^ 2 * r1 ^ (K - 2) + (K : ℝ) ^ 2 * r2 ^ (K - 2)) ≤
      routingProb μ C K := by
  set P := Measure.pi fun _ : Edge K => μ with hP
  have hcast : ((K - 2 : ℕ) : ℝ) = (K : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  set Bad : Set (Edge K → ℝ) := {x | ∃ g, x g < 0} ∪
    ⋃ p : {p : Fin K × Fin K // p.1 ≠ p.2},
      pairMap p.1.1 p.1.2 ⁻¹' (A1 C D (T p.1.1 p.1.2) ∪ A2 C D (T p.1.1 p.1.2)) with hBad
  -- step 1: off the bad set the loads are routable
  have hsub : Badᶜ ⊆ {x | Feasible C x} := by
    intro x hx
    have hx' : x ∉ Bad := hx
    have hx0 : ∀ g, 0 ≤ x g := by
      intro g
      by_contra h
      exact hx' (Set.mem_union_left _ ⟨g, lt_of_not_ge h⟩)
    have hp : ∀ a b : Fin K, ∀ hab : a ≠ b,
        pairMap a b x ∉ A1 C D (T a b) ∧ pairMap a b x ∉ A2 C D (T a b) := by
      intro a b hab
      constructor
      · intro h
        exact hx' (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨⟨(a, b), hab⟩, Or.inl h⟩))
      · intro h
        exact hx' (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨⟨(a, b), hab⟩, Or.inr h⟩))
    apply good_feasible C D hC hD hK x hx0
    · intro a b hab
      have h := (hp a b hab).1
      simp only [A1, Set.mem_setOf_eq, not_le, Finset.sum_neg_distrib, card_T a b hab,
        hcast] at h
      linarith
    · intro a b hab
      have h := (hp a b hab).2
      simp only [A2, Set.mem_setOf_eq, not_le, card_T a b hab, hcast] at h
      linarith
  -- step 2: negative loads are null
  have hN : P {x : Edge K → ℝ | ∃ g, x g < 0} = 0 := by
    have hset : {x : Edge K → ℝ | ∃ g, x g < 0} = ⋃ g, (fun x => x g) ⁻¹' Set.Iio 0 := by
      ext x; simp
    rw [hset]
    apply measure_iUnion_null
    intro g
    rw [(measurePreserving_eval (fun _ : Edge K => μ) g).measure_preimage
      measurableSet_Iio.nullMeasurableSet]
    have h0 := ae_iff.mp hnonneg
    have hI : Set.Iio (0 : ℝ) = {a | ¬ 0 ≤ a} := by ext; simp
    rw [hI]; exact h0
  -- step 3: each pair contributes at most `r1^(K-2) + r2^(K-2)`
  have hpre : ∀ a b : Fin K, ∀ hab : a ≠ b,
      P (pairMap a b ⁻¹' (A1 C D (T a b) ∪ A2 C D (T a b))) ≤
        ENNReal.ofReal (r1 ^ (K - 2)) + ENNReal.ofReal (r2 ^ (K - 2)) := by
    intro a b hab
    rw [Set.preimage_union]
    refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
    · rw [(pairMap_mp μ a b hab).measure_preimage (measurableSet_A1 C D _).nullMeasurableSet,
        ← ofReal_measureReal (measure_ne_top _ _)]
      have := hr1 (T a b)
      rw [card_T a b hab] at this
      exact ENNReal.ofReal_le_ofReal this
    · rw [(pairMap_mp μ a b hab).measure_preimage (measurableSet_A2 C D _).nullMeasurableSet,
        ← ofReal_measureReal (measure_ne_top _ _)]
      have := hr2 (T a b)
      rw [card_T a b hab] at this
      exact ENNReal.ofReal_le_ofReal this
  -- step 4: union bound
  have hcard : Fintype.card {p : Fin K × Fin K // p.1 ≠ p.2} ≤ K ^ 2 := by
    refine (Fintype.card_subtype_le _).trans ?_
    simp [Fintype.card_prod, sq]
  have hBadle : P Bad ≤ (K : ENNReal) ^ 2 *
      (ENNReal.ofReal (r1 ^ (K - 2)) + ENNReal.ofReal (r2 ^ (K - 2))) := by
    calc P Bad ≤ P {x : Edge K → ℝ | ∃ g, x g < 0} + P (⋃ p : {p : Fin K × Fin K // p.1 ≠ p.2},
          pairMap p.1.1 p.1.2 ⁻¹' (A1 C D (T p.1.1 p.1.2) ∪ A2 C D (T p.1.1 p.1.2))) :=
          measure_union_le _ _
      _ = P (⋃ p : {p : Fin K × Fin K // p.1 ≠ p.2},
          pairMap p.1.1 p.1.2 ⁻¹' (A1 C D (T p.1.1 p.1.2) ∪ A2 C D (T p.1.1 p.1.2))) := by
          rw [hN, zero_add]
      _ ≤ ∑ p : {p : Fin K × Fin K // p.1 ≠ p.2},
          P (pairMap p.1.1 p.1.2 ⁻¹' (A1 C D (T p.1.1 p.1.2) ∪ A2 C D (T p.1.1 p.1.2))) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _p : {p : Fin K × Fin K // p.1 ≠ p.2},
          (ENNReal.ofReal (r1 ^ (K - 2)) + ENNReal.ofReal (r2 ^ (K - 2))) :=
          Finset.sum_le_sum fun p _ => hpre p.1.1 p.1.2 p.2
      _ = (Fintype.card {p : Fin K × Fin K // p.1 ≠ p.2} : ENNReal) *
          (ENNReal.ofReal (r1 ^ (K - 2)) + ENNReal.ofReal (r2 ^ (K - 2))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := by
          gcongr
          exact_mod_cast hcard
  have hconv : ENNReal.ofReal ((K : ℝ) ^ 2 * r1 ^ (K - 2) + (K : ℝ) ^ 2 * r2 ^ (K - 2)) =
      (K : ENNReal) ^ 2 * (ENNReal.ofReal (r1 ^ (K - 2)) + ENNReal.ofReal (r2 ^ (K - 2))) := by
    rw [ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (pow_nonneg hr10 _))
      (mul_nonneg (sq_nonneg _) (pow_nonneg hr20 _)),
      ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _),
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_add]
  unfold routingProb
  rw [← hP, hconv]
  calc 1 - (K : ENNReal) ^ 2 * (ENNReal.ofReal (r1 ^ (K - 2)) + ENNReal.ofReal (r2 ^ (K - 2)))
      ≤ 1 - P Bad := tsub_le_tsub_left hBadle 1
    _ ≤ P Badᶜ := by
        rw [tsub_le_iff_left]
        calc (1 : ENNReal) = P Set.univ := measure_univ.symm
          _ = P (Bad ∪ Badᶜ) := by rw [Set.union_compl_self]
          _ ≤ P Bad + P Badᶜ := measure_union_le _ _
    _ ≤ P {x | Feasible C x} := measure_mono hsub

theorem exp_plus_le (θ C t : ℝ) (hθ : 0 ≤ θ) (hC : 0 ≤ C) :
    Real.exp (θ * max (t - C) 0) ≤ 1 + Real.exp (θ * t) := by
  rcases le_total (t - C) 0 with h | h
  · rw [max_eq_right h, mul_zero, Real.exp_zero]
    linarith [Real.exp_pos (θ * t)]
  · rw [max_eq_left h]
    have : Real.exp (θ * (t - C)) ≤ Real.exp (θ * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith [Real.exp_pos (θ * t)]

end KellyLossNetworks.Routing.Aux

open KellyLossNetworks.Routing.Aux

open MeasureTheory Filter Topology KellyLossNetworks.Routing in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t)
    (C : ℝ) (hmgf : ∃ θ : ℝ, 0 < θ ∧ Integrable (fun t => Real.exp (θ * t)) μ)
    (h446 : 2 * ∫ t, max (t - C) 0 ∂μ < ∫ t, max (C - t) 0 ∂μ) :
    Tendsto (fun K : ℕ => routingProb μ C K) atTop (𝓝 1) := by
  obtain ⟨θ, hθ, hθint⟩ := hmgf
  have he0 : 0 ≤ ∫ t, max (t - C) 0 ∂μ := integral_nonneg fun t => le_max_right _ _
  have hC : 0 < C := by
    by_contra hC
    have hC' : C ≤ 0 := not_lt.mp hC
    have : ∫ t, max (C - t) 0 ∂μ = 0 :=
      integral_eq_zero_of_ae (by filter_upwards [hnonneg] with t ht; exact max_eq_right (by linarith))
    linarith
  -- integrability of the ingredients
  have hint_gC : Integrable (gC C) μ :=
    Integrable.mono' (integrable_const C) (measurable_gC C).aestronglyMeasurable
      (ae_of_all _ fun t => by
        rw [Real.norm_of_nonneg (gC_nonneg hC.le t)]; exact gC_le C t)
  have hint_plus : Integrable (fun t => max (t - C) 0) μ :=
    Integrable.mono' (hθint.div_const θ)
      ((measurable_id.sub_const C).max measurable_const).aestronglyMeasurable
      (ae_of_all _ fun t => by
        rw [Real.norm_of_nonneg (le_max_right _ _), le_div_iff₀ hθ]
        rcases le_total (t - C) 0 with h | h
        · rw [max_eq_right h, zero_mul]; exact (Real.exp_pos _).le
        · rw [max_eq_left h]
          nlinarith [Real.add_one_le_exp (θ * t), mul_nonneg hC.le hθ.le])
  have intgC : ∫ t, gC C t ∂μ = ∫ t, max (C - t) 0 ∂μ :=
    integral_congr_ae (by filter_upwards [hnonneg] with t ht; exact gC_of_nonneg hC.le ht)
  set s := ∫ t, max (C - t) 0 ∂μ with hs_def
  set e := ∫ t, max (t - C) 0 ∂μ with he_def
  have hs : 0 < s := by linarith
  have h2es : 2 * e * s < s ^ 2 := by nlinarith
  set D : ℝ := (s ^ 2 + 2 * e * s) / 2 with hD_def
  have hD : 0 < D := by rw [hD_def]; nlinarith
  have hDY : D < s ^ 2 := by rw [hD_def]; linarith
  have hDZ : 2 * e * s < D := by rw [hD_def]; linarith
  -- moments
  have intY : ∫ p, Yc C p ∂(μ.prod μ) = s ^ 2 := by
    have : ∫ p, Yc C p ∂(μ.prod μ) = (∫ t, gC C t ∂μ) * ∫ t, gC C t ∂μ :=
      integral_prod_mul (gC C) (gC C)
    rw [this, intgC, sq]
  have intZ : ∫ p, Zc C p ∂(μ.prod μ) = 2 * e * s := by
    have hi1 : Integrable (fun p : ℝ × ℝ => max (p.1 - C) 0 * gC C p.2) (μ.prod μ) :=
      hint_plus.mul_prod hint_gC
    have hi2 : Integrable (fun p : ℝ × ℝ => max (p.2 - C) 0 * gC C p.1) (μ.prod μ) :=
      (hint_gC.mul_prod hint_plus).congr (ae_of_all _ fun p => mul_comm _ _)
    have e1 : ∫ p : ℝ × ℝ, max (p.1 - C) 0 * gC C p.2 ∂(μ.prod μ) = e * s := by
      rw [integral_prod_mul (fun t => max (t - C) 0) (gC C), intgC]
    have e2 : ∫ p : ℝ × ℝ, max (p.2 - C) 0 * gC C p.1 ∂(μ.prod μ) = s * e := by
      have : ∫ p : ℝ × ℝ, max (p.2 - C) 0 * gC C p.1 ∂(μ.prod μ) =
          ∫ p : ℝ × ℝ, gC C p.1 * max (p.2 - C) 0 ∂(μ.prod μ) :=
        integral_congr_ae (ae_of_all _ fun p => mul_comm _ _)
      rw [this, integral_prod_mul (gC C) (fun t => max (t - C) 0), intgC]
    unfold Zc
    rw [integral_add hi1 hi2, e1, e2]
    ring
  -- Chernoff for Y
  obtain ⟨r1, hr10, hr11, hr1⟩ := chernoff_iid (μ.prod μ) (fun p => -Yc C p)
    (measurable_Yc C).neg (C ^ 2) (fun p => by have := Yc_le hC.le p; linarith) (-D)
    (by rw [integral_neg, intY]; linarith) 1 one_pos
    (Integrable.mono' (integrable_const (1 : ℝ))
      ((measurable_Yc C).neg.const_mul 1).exp.aestronglyMeasurable
      (ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
        have := Yc_nonneg hC.le p
        linarith))
  -- Chernoff for Z
  have hone : Integrable (fun t => 1 + Real.exp (θ * t)) μ := (integrable_const 1).add hθint
  have hZpt : ∀ p : ℝ × ℝ, Real.exp (θ / C * Zc C p) ≤
      (1 + Real.exp (θ * p.1)) * (1 + Real.exp (θ * p.2)) := by
    intro p
    have h1 : Zc C p ≤ C * (max (p.1 - C) 0 + max (p.2 - C) 0) := by
      unfold Zc
      nlinarith [gC_le C p.1, gC_le C p.2, le_max_right (p.1 - C) 0, le_max_right (p.2 - C) 0]
    have hZ : θ / C * Zc C p ≤ θ * max (p.1 - C) 0 + θ * max (p.2 - C) 0 := by
      calc θ / C * Zc C p ≤ θ / C * (C * (max (p.1 - C) 0 + max (p.2 - C) 0)) :=
            mul_le_mul_of_nonneg_left h1 (div_nonneg hθ.le hC.le)
        _ = θ * max (p.1 - C) 0 + θ * max (p.2 - C) 0 := by field_simp
    calc Real.exp (θ / C * Zc C p)
        ≤ Real.exp (θ * max (p.1 - C) 0 + θ * max (p.2 - C) 0) := Real.exp_le_exp.mpr hZ
      _ = Real.exp (θ * max (p.1 - C) 0) * Real.exp (θ * max (p.2 - C) 0) := Real.exp_add _ _
      _ ≤ _ := mul_le_mul (exp_plus_le θ C p.1 hθ.le hC.le) (exp_plus_le θ C p.2 hθ.le hC.le)
            (Real.exp_pos _).le (by positivity)
  obtain ⟨r2, hr20, hr21, hr2⟩ := chernoff_iid (μ.prod μ) (Zc C) (measurable_Zc C) 0
    (fun p => by have := Zc_nonneg hC.le p; linarith) D (by rw [intZ]; exact hDZ)
    (θ / C) (div_pos hθ hC)
    (Integrable.mono' (hone.mul_prod hone)
      ((measurable_Zc C).const_mul (θ / C)).exp.aestronglyMeasurable
      (ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hZpt p))
  -- limit
  have hlim : Tendsto (fun K : ℕ => (K : ℝ) ^ 2 * r1 ^ (K - 2) + (K : ℝ) ^ 2 * r2 ^ (K - 2))
      atTop (𝓝 0) := by
    simpa using (tendsto_sq_mul_pow_sub_two r1 hr10 hr11).add
      (tendsto_sq_mul_pow_sub_two r2 hr20 hr21)
  have hlow : Tendsto (fun K : ℕ =>
      1 - ENNReal.ofReal ((K : ℝ) ^ 2 * r1 ^ (K - 2) + (K : ℝ) ^ 2 * r2 ^ (K - 2)))
      atTop (𝓝 1) := by
    have h := ENNReal.tendsto_ofReal hlim
    rw [ENNReal.ofReal_zero] at h
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl ENNReal.one_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with K hK
    exact prob_bad μ hnonneg C D hC hD r1 r2 hr10 hr20 (fun S _ => hr1 S) (fun S _ => hr2 S) K hK
  · exact Eventually.of_forall fun K => by unfold routingProb; exact prob_le_one
