-- Prove2me | solution 1 for HealthRefPricing.PriceCompare.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:00.563448+00:00
-- url     : https://prove2.me/submissions/efe9c681-7891-41e0-915e-25f20ef6a75b

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Supplement_ERP

open HealthRefPricing
open HealthRefPricing.PriceCompare
open HealthRefPricing.PriceCompare.Supplement

/-- Theorem 3, corrected at the interval endpoints and at equality of the regime threshold.
Assumption 3 is unnecessary for the log-profit best-response argument. -/
theorem solution (P : Params) (hS : P.Standing) :
    let B := Real.exp P.u0 + Real.exp (P.a 0 - P.γ * P.ct)
    let E := Real.exp (P.a 1 - P.γ * P.ct)
    let L := P.c + (B + E) / (P.γ * B)
    let U := P.c + (B + E) / (P.γ * E)
    (E ≤ B → ∀ p : Fin 2 → ℝ,
      IsEqERP P p ↔ p 0 = p 1 ∧ p 0 ∈ Set.Icc L U) ∧
    (E < B → Set.Infinite {p : Fin 2 → ℝ | IsEqERP P p}) ∧
    (E = B → ∃! p : Fin 2 → ℝ, IsEqERP P p) ∧
    (B < E → (∃! p : Fin 2 → ℝ, IsEqERP P p) ∧
      ∀ p : Fin 2 → ℝ, IsEqERP P p →
        p 0 < p 1 ∧
        Real.exp (P.a 1 - P.γ * (p 1 - p 0 + P.ct)) =
          B * (P.γ * (p 1 - P.c) - 1) ∧
        P.γ * (p 0 - P.c) - 1 = 1 / (P.γ * (p 1 - P.c) - 1) ∧
        ∀ q : Fin 2 → ℝ,
          Real.exp (P.a 1 - P.γ * (q 1 - q 0 + P.ct)) =
            B * (P.γ * (q 1 - P.c) - 1) →
          P.γ * (q 0 - P.c) - 1 = 1 / (P.γ * (q 1 - P.c) - 1) → q = p) := by
            intro B E L U
            obtain ⟨hm, hγ, hc, ha, hct⟩ := hS
            have hB : B = Real.exp P.u0 + Real.exp (P.a 0 - P.γ * P.ct) := rfl
            have hE : E = Real.exp (P.a 1 - P.γ * P.ct) := rfl
            have hL : L = P.c + (B + E) / (P.γ * B) := rfl
            have hU : U = P.c + (B + E) / (P.γ * E) := rfl
            clear_value L U B E
            obtain ⟨e, he⟩ : ∃ e, e = Real.exp P.u0 := ⟨_, rfl⟩
            obtain ⟨A0, hA0⟩ : ∃ x, x = Real.exp (P.a 0 - P.γ * P.ct) := ⟨_, rfl⟩
            obtain ⟨A1, hA1⟩ : ∃ x, x = Real.exp (P.a 1 - P.γ * P.ct) := ⟨_, rfl⟩
            have he0 : 0 < e := he ▸ Real.exp_pos _
            have hA0p : 0 < A0 := hA0 ▸ Real.exp_pos _
            have hA1p : 0 < A1 := hA1 ▸ Real.exp_pos _
            have hA01 : A0 ≤ A1 := by rw [hA0, hA1]; exact Real.exp_le_exp.mpr (sub_le_sub_right ha _)
            rw [← he, ← hA0] at hB
            rw [← hA1] at hE
            obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ → ℝ → ℝ → ℝ, ∀ α β y x, D α β y x =
                e * Real.exp (P.γ * max 0 (x - y)) + α + β * Real.exp (P.γ * (x - y)) :=
              ⟨_, fun _ _ _ _ => rfl⟩
            have H0 : ∀ (p : Fin 2 → ℝ) (x : ℝ), profitERP P (Function.update p 0 x) 0
                = P.m * (x - P.c) * A0 / D A0 A1 (p 1) x := by
              intro p x
              simp only [profitERP, share, oopERP, Fin.sum_univ_two, Function.update_self,
                Function.update_of_ne (show (1:Fin 2) ≠ 0 by decide)]
              rw [hD, mul_div_assoc]
              congr 1
              rcases le_total x (p 1) with h | h
              · rw [min_eq_left h, sub_self, max_self, max_eq_left (by linarith : x - p 1 ≤ 0),
                  max_eq_right (by linarith : 0 ≤ p 1 - x)]
                have h1 : Real.exp (P.a 1 - P.γ * (P.ct + (p 1 - x))) = A1 * Real.exp (P.γ * (x - p 1)) := by
                  rw [hA1, ← Real.exp_add]; congr 1; ring
                rw [h1]; simp only [add_zero, mul_zero, Real.exp_zero, mul_one]; rw [← hA0, ← he]; ring
              · rw [min_eq_right h, sub_self, max_self, max_eq_right (by linarith : 0 ≤ x - p 1)]
                have h1 : Real.exp (P.a 0 - P.γ * (P.ct + (x - p 1))) = A0 * Real.exp (-(P.γ * (x - p 1))) := by
                  rw [hA0, ← Real.exp_add]; congr 1; ring
                have h2 : Real.exp (-(P.γ * (x - p 1))) * Real.exp (P.γ * (x - p 1)) = 1 := by
                  rw [← Real.exp_add]; simp
                rw [h1]; simp only [add_zero]; rw [← hA1, ← he]
                have hp1 : 0 < Real.exp (-(P.γ * (x - p 1))) := Real.exp_pos _
                have hp2 : 0 < Real.exp (P.γ * (x - p 1)) := Real.exp_pos _
                rw [div_eq_div_iff (by positivity) (by positivity)]
                linear_combination (A0 * (e + A1)) * h2
            have H1 : ∀ (p : Fin 2 → ℝ) (x : ℝ), profitERP P (Function.update p 1 x) 1
                = P.m * (x - P.c) * A1 / D A1 A0 (p 0) x := by
              intro p x
              simp only [profitERP, share, oopERP, Fin.sum_univ_two, Function.update_self,
                Function.update_of_ne (show (0:Fin 2) ≠ 1 by decide)]
              rw [hD, mul_div_assoc]
              congr 1
              rcases le_total x (p 0) with h | h
              · rw [min_eq_right h, sub_self, max_self, max_eq_left (by linarith : x - p 0 ≤ 0),
                  max_eq_right (by linarith : 0 ≤ p 0 - x)]
                have h1 : Real.exp (P.a 0 - P.γ * (P.ct + (p 0 - x))) = A0 * Real.exp (P.γ * (x - p 0)) := by
                  rw [hA0, ← Real.exp_add]; congr 1; ring
                rw [h1]; simp only [add_zero, mul_zero, Real.exp_zero, mul_one]; rw [← hA1, ← he]; ring
              · rw [min_eq_left h, sub_self, max_self, max_eq_right (by linarith : 0 ≤ x - p 0)]
                have h1 : Real.exp (P.a 1 - P.γ * (P.ct + (x - p 0))) = A1 * Real.exp (-(P.γ * (x - p 0))) := by
                  rw [hA1, ← Real.exp_add]; congr 1; ring
                have h2 : Real.exp (-(P.γ * (x - p 0))) * Real.exp (P.γ * (x - p 0)) = 1 := by
                  rw [← Real.exp_add]; simp
                rw [h1]; simp only [add_zero]; rw [← hA0, ← he]
                have hp1 : 0 < Real.exp (-(P.γ * (x - p 0))) := Real.exp_pos _
                have hp2 : 0 < Real.exp (P.γ * (x - p 0)) := Real.exp_pos _
                rw [div_eq_div_iff (by positivity) (by positivity)]
                linear_combination (A1 * (e + A0)) * h2
            have DF1 : ∀ α β y x, x ≤ y → D α β y x = e + α + β * Real.exp (P.γ * (x - y)) := by
              intro α β y x h; rw [hD, max_eq_left (sub_nonpos.mpr h), mul_zero, Real.exp_zero, mul_one]
            have DF2 : ∀ α β y x, y ≤ x → D α β y x = α + (e + β) * Real.exp (P.γ * (x - y)) := by
              intro α β y x h; rw [hD, max_eq_right (sub_nonneg.mpr h)]; ring
            have DF3 : ∀ α β y x, e + α + β * Real.exp (P.γ * (x - y)) ≤ D α β y x := by
              intro α β y x; rw [hD]
              have : 1 ≤ Real.exp (P.γ * max 0 (x - y)) :=
                Real.one_le_exp (mul_nonneg hγ.le (le_max_left _ _))
              linarith only [le_mul_of_one_le_right he0.le this]
            have DF4 : ∀ α β y x, α + (e + β) * Real.exp (P.γ * (x - y)) ≤ D α β y x := by
              intro α β y x; rw [hD]
              have : Real.exp (P.γ * (x - y)) ≤ Real.exp (P.γ * max 0 (x - y)) :=
                Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_max_right _ _) hγ.le)
              linarith only [mul_le_mul_of_nonneg_left this he0.le]
            have Dpos : ∀ α β y x, 0 < α → 0 ≤ β → 0 < D α β y x := by
              intro α β y x hα hβ; rw [hD]; positivity
            have expsplit : ∀ x x0 y, Real.exp (P.γ * (x - y)) =
                Real.exp (P.γ * (x0 - y)) * Real.exp (P.γ * (x - x0)) := by
              intro x x0 y; rw [← Real.exp_add]; congr 1; ring
            have T : ∀ Q R u v : ℝ, 0 < v → 0 ≤ R → (u - v) * (Q + R - P.γ * v * R) ≤ 0 →
                u * (Q + R) ≤ v * (Q + R * Real.exp (P.γ * (u - v))) := by
              intro Q R u v hv hR h
              have h1 := Real.add_one_le_exp (P.γ * (u - v))
              have h2 : v * R * (P.γ * (u - v) + 1) ≤ v * R * Real.exp (P.γ * (u - v)) :=
                mul_le_mul_of_nonneg_left h1 (mul_nonneg hv.le hR)
              linarith only [h, h2]
            have SMALL : ∀ Z K δ0 : ℝ, 0 < K → 0 < δ0 →
                (∀ δ, 0 < δ → δ < δ0 → P.γ * δ ≤ 1 → Z ≤ K * δ) → Z ≤ 0 := by
              intro Z K δ0 hK hδ0 h
              by_contra hZ'
              have hZ : 0 < Z := lt_of_not_ge hZ'
              have hδpos : 0 < min (δ0 / 2) (min (1 / P.γ) (Z / (2 * K))) := by
                apply lt_min (by linarith only [hδ0]) (lt_min (by positivity) (by positivity))
              have hδ1 : min (δ0 / 2) (min (1 / P.γ) (Z / (2 * K))) ≤ δ0 / 2 := min_le_left _ _
              have hδ2 : min (δ0 / 2) (min (1 / P.γ) (Z / (2 * K))) ≤ 1 / P.γ :=
                (min_le_right _ _).trans (min_le_left _ _)
              have hδ3 : min (δ0 / 2) (min (1 / P.γ) (Z / (2 * K))) ≤ Z / (2 * K) :=
                (min_le_right _ _).trans (min_le_right _ _)
              generalize min (δ0 / 2) (min (1 / P.γ) (Z / (2 * K))) = δ at hδpos hδ1 hδ2 hδ3
              rw [le_div_iff₀ hγ] at hδ2
              rw [le_div_iff₀ (by positivity)] at hδ3
              have := h δ hδpos (by linarith only [hδ1, hδ0]) (by linarith only [hδ2])
              linarith only [this, hδ3, hZ]
            have NR : ∀ Q R v δ0 : ℝ, 0 < v → 0 < R → 0 < δ0 →
                (∀ δ, 0 < δ → δ < δ0 → (v + δ) * (Q + R) ≤ v * (Q + R * Real.exp (P.γ * δ))) →
                Q + R - P.γ * v * R ≤ 0 := by
              intro Q R v δ0 hv hR hδ0 h
              apply SMALL _ (v * R * P.γ ^ 2) δ0 (by positivity) hδ0
              intro δ hδ hδδ hγδ
              have hexp : Real.exp (P.γ * δ) ≤ 1 + P.γ * δ + (P.γ * δ) ^ 2 := by
                have := Real.abs_exp_sub_one_sub_id_le (x := P.γ * δ)
                  (by rw [abs_of_pos (by positivity)]; exact hγδ)
                have := (abs_le.mp this).2
                linarith only [this]
              have hh := h δ hδ hδδ
              have h3 : v * R * Real.exp (P.γ * δ) ≤ v * R * (1 + P.γ * δ + (P.γ * δ) ^ 2) :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
              have h4 : δ * (Q + R - P.γ * v * R) ≤ δ * (v * R * P.γ ^ 2 * δ) := by linarith only [hh, h3]
              exact le_of_mul_le_mul_left h4 hδ
            have NL : ∀ Q R v δ0 : ℝ, 0 < v → 0 < R → 0 < δ0 →
                (∀ δ, 0 < δ → δ < δ0 → (v - δ) * (Q + R) ≤ v * (Q + R * Real.exp (-(P.γ * δ)))) →
                P.γ * v * R - (Q + R) ≤ 0 := by
              intro Q R v δ0 hv hR hδ0 h
              apply SMALL _ (v * R * P.γ ^ 2) δ0 (by positivity) hδ0
              intro δ hδ hδδ hγδ
              have hexp : Real.exp (-(P.γ * δ)) ≤ 1 - P.γ * δ + (P.γ * δ) ^ 2 := by
                have := Real.abs_exp_sub_one_sub_id_le (x := -(P.γ * δ))
                  (by rw [abs_neg, abs_of_pos (by positivity)]; exact hγδ)
                have := (abs_le.mp this).2
                linarith only [this]
              have hh := h δ hδ hδδ
              have h3 : v * R * Real.exp (-(P.γ * δ)) ≤ v * R * (1 - P.γ * δ + (P.γ * δ) ^ 2) :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
              have h4 : δ * (P.γ * v * R - (Q + R)) ≤ δ * (v * R * P.γ ^ 2 * δ) := by linarith only [hh, h3]
              exact le_of_mul_le_mul_left h4 hδ
            obtain ⟨Cond, hCond⟩ : ∃ Cond : ℝ → ℝ → ℝ → ℝ → Prop, ∀ α β y x0, Cond α β y x0 ↔
                ((x0 < y ∧ e + α + β * Real.exp (P.γ * (x0 - y)) =
                    P.γ * (x0 - P.c) * (β * Real.exp (P.γ * (x0 - y)))) ∨
                 (x0 = y ∧ P.γ * β * (y - P.c) ≤ e + α + β ∧ e + α + β ≤ P.γ * (e + β) * (y - P.c)) ∨
                 (y < x0 ∧ α + (e + β) * Real.exp (P.γ * (x0 - y)) =
                    P.γ * (x0 - P.c) * ((e + β) * Real.exp (P.γ * (x0 - y))))) :=
              ⟨_, fun _ _ _ _ => Iff.rfl⟩
            have KEY : ∀ α β y x0 : ℝ, 0 < α → 0 < β →
                ((∀ x, (x - P.c) * D α β y x0 ≤ (x0 - P.c) * D α β y x) ↔ Cond α β y x0) := by
              intro α β y x0 hα hβ
              rw [hCond]
              constructor
              · intro h
                have hv : 0 < x0 - P.c := by
                  have h1 := h (P.c + 1)
                  have := Dpos α β y x0 hα hβ.le
                  have := Dpos α β y (P.c + 1) hα hβ.le
                  by_contra hv'
                  have hv : x0 - P.c ≤ 0 := le_of_not_gt hv'
                  have := mul_nonpos_of_nonpos_of_nonneg hv (Dpos α β y (P.c + 1) hα hβ.le).le
                  linarith only [h1, this, Dpos α β y x0 hα hβ.le]
                rcases lt_trichotomy x0 y with hlt | heq | hgt
                · left; refine ⟨hlt, ?_⟩
                  have hR : 0 < β * Real.exp (P.γ * (x0 - y)) := by positivity
                  have r1 := NR (e + α) (β * Real.exp (P.γ * (x0 - y))) (x0 - P.c) (y - x0) hv hR
                    (sub_pos.mpr hlt) (by
                      intro δ hδ hδ0
                      have := h (x0 + δ)
                      rw [DF1 α β y x0 hlt.le, DF1 α β y (x0 + δ) (by linarith only [hδ0]),
                        expsplit (x0 + δ) x0 y, show x0 + δ - x0 = δ by ring] at this
                      linarith only [this])
                  have r2 := NL (e + α) (β * Real.exp (P.γ * (x0 - y))) (x0 - P.c) (y - x0) hv hR
                    (sub_pos.mpr hlt) (by
                      intro δ hδ hδ0
                      have := h (x0 - δ)
                      rw [DF1 α β y x0 hlt.le, DF1 α β y (x0 - δ) (by linarith only [hδ, hlt]),
                        expsplit (x0 - δ) x0 y, show P.γ * (x0 - δ - x0) = -(P.γ * δ) by ring] at this
                      linarith only [this])
                  linarith only [r1, r2]
                · right; left; subst heq; refine ⟨rfl, ?_, ?_⟩
                  · have r2 := NL (e + α) β (x0 - P.c) 1 hv hβ (by norm_num) (by
                      intro δ hδ _
                      have := h (x0 - δ)
                      rw [DF1 α β x0 x0 le_rfl, DF1 α β x0 (x0 - δ) (by linarith only [hδ]),
                        show P.γ * (x0 - δ - x0) = -(P.γ * δ) by ring, sub_self x0, mul_zero P.γ,
                        Real.exp_zero] at this
                      linarith only [this])
                    linarith only [r2]
                  · have r1 := NR α (e + β) (x0 - P.c) 1 hv (by positivity) (by norm_num) (by
                      intro δ hδ _
                      have := h (x0 + δ)
                      rw [DF2 α β x0 x0 le_rfl, DF2 α β x0 (x0 + δ) (by linarith only [hδ]),
                        show x0 + δ - x0 = δ by ring, sub_self x0, mul_zero P.γ,
                        Real.exp_zero] at this
                      linarith only [this])
                    linarith only [r1]
                · right; right; refine ⟨hgt, ?_⟩
                  have hR : 0 < (e + β) * Real.exp (P.γ * (x0 - y)) := by positivity
                  have r1 := NR α ((e + β) * Real.exp (P.γ * (x0 - y))) (x0 - P.c) (x0 - y) hv hR
                    (sub_pos.mpr hgt) (by
                      intro δ hδ hδ0
                      have := h (x0 + δ)
                      rw [DF2 α β y x0 hgt.le, DF2 α β y (x0 + δ) (by linarith only [hδ, hgt]),
                        expsplit (x0 + δ) x0 y, show x0 + δ - x0 = δ by ring] at this
                      linarith only [this])
                  have r2 := NL α ((e + β) * Real.exp (P.γ * (x0 - y))) (x0 - P.c) (x0 - y) hv hR
                    (sub_pos.mpr hgt) (by
                      intro δ hδ hδ0
                      have := h (x0 - δ)
                      rw [DF2 α β y x0 hgt.le, DF2 α β y (x0 - δ) (by linarith only [hδ0]),
                        expsplit (x0 - δ) x0 y, show P.γ * (x0 - δ - x0) = -(P.γ * δ) by ring] at this
                      linarith only [this])
                  linarith only [r1, r2]
              · intro hC x
                rcases hC with ⟨hlt, heq⟩ | ⟨hxy, h1, h2⟩ | ⟨hgt, heq⟩
                · have hR : 0 < β * Real.exp (P.γ * (x0 - y)) := by positivity
                  have hv : 0 < x0 - P.c := by
                    by_contra hv'
                    have hv : x0 - P.c ≤ 0 := le_of_not_gt hv'
                    have : P.γ * (x0 - P.c) * (β * Real.exp (P.γ * (x0 - y))) ≤ 0 :=
                      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hγ.le hv) hR.le
                    linarith only [this, heq, he0, hα, hR]
                  have t := T (e + α) (β * Real.exp (P.γ * (x0 - y))) (x - P.c) (x0 - P.c) hv hR.le
                    (by rw [sub_eq_zero.mpr heq]; exact le_of_eq (mul_zero _))
                  rw [show x - P.c - (x0 - P.c) = x - x0 by ring] at t
                  have d3 := DF3 α β y x
                  rw [expsplit x x0 y] at d3
                  rw [DF1 α β y x0 hlt.le]
                  have := mul_le_mul_of_nonneg_left d3 hv.le
                  linarith only [this, t]
                · subst hxy
                  have hv : 0 < x0 - P.c := by
                    by_contra hv'
                    have hv : x0 - P.c ≤ 0 := le_of_not_gt hv'
                    have : P.γ * (e + β) * (x0 - P.c) ≤ 0 :=
                      mul_nonpos_of_nonneg_of_nonpos (by positivity) hv
                    linarith only [this, h2, he0, hα, hβ]
                  rcases le_total x x0 with hx | hx
                  · have t := T (e + α) β (x - P.c) (x0 - P.c) hv hβ.le
                      (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hx]) (by linarith only [h1]))
                    rw [show x - P.c - (x0 - P.c) = x - x0 by ring] at t
                    have d3 := DF3 α β x0 x
                    rw [DF1 α β x0 x0 le_rfl, sub_self x0, mul_zero P.γ, Real.exp_zero]
                    have := mul_le_mul_of_nonneg_left d3 hv.le
                    linarith only [this, t]
                  · have t := T α (e + β) (x - P.c) (x0 - P.c) hv (by positivity)
                      (mul_nonpos_of_nonneg_of_nonpos (by linarith only [hx]) (by linarith only [h2]))
                    rw [show x - P.c - (x0 - P.c) = x - x0 by ring] at t
                    have d4 := DF4 α β x0 x
                    rw [DF2 α β x0 x0 le_rfl, sub_self x0, mul_zero P.γ, Real.exp_zero]
                    have := mul_le_mul_of_nonneg_left d4 hv.le
                    linarith only [this, t]
                · have hR : 0 < (e + β) * Real.exp (P.γ * (x0 - y)) := by positivity
                  have hv : 0 < x0 - P.c := by
                    by_contra hv'
                    have hv : x0 - P.c ≤ 0 := le_of_not_gt hv'
                    have : P.γ * (x0 - P.c) * ((e + β) * Real.exp (P.γ * (x0 - y))) ≤ 0 :=
                      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hγ.le hv) hR.le
                    linarith only [this, heq, he0, hα, hR]
                  have t := T α ((e + β) * Real.exp (P.γ * (x0 - y))) (x - P.c) (x0 - P.c) hv hR.le
                    (by rw [sub_eq_zero.mpr heq]; exact le_of_eq (mul_zero _))
                  rw [show x - P.c - (x0 - P.c) = x - x0 by ring] at t
                  have d4 := DF4 α β y x
                  rw [expsplit x x0 y] at d4
                  rw [DF2 α β y x0 hgt.le]
                  have := mul_le_mul_of_nonneg_left d4 hv.le
                  linarith only [this, t]
            subst B E
            have hBp : 0 < e + A0 := by positivity
            have PR0 : ∀ (p : Fin 2 → ℝ) (x : ℝ),
                profitERP P (Function.update p 0 x) 0 ≤ profitERP P p 0 ↔
                (x - P.c) * D A0 A1 (p 1) (p 0) ≤ (p 0 - P.c) * D A0 A1 (p 1) x := by
              intro p x
              have hp : profitERP P p 0 = profitERP P (Function.update p 0 (p 0)) 0 := by
                rw [Function.update_eq_self]
              have k : 0 < P.m * A0 := mul_pos hm hA0p
              rw [hp, H0 p x, H0 p (p 0), div_le_div_iff₀ (Dpos _ _ _ _ hA0p hA1p.le) (Dpos _ _ _ _ hA0p hA1p.le),
                show P.m * (x - P.c) * A0 * D A0 A1 (p 1) (p 0) = (P.m * A0) * ((x - P.c) * D A0 A1 (p 1) (p 0)) by ring,
                show P.m * (p 0 - P.c) * A0 * D A0 A1 (p 1) x = (P.m * A0) * ((p 0 - P.c) * D A0 A1 (p 1) x) by ring]
              exact mul_le_mul_iff_of_pos_left k
            have PR1 : ∀ (p : Fin 2 → ℝ) (x : ℝ),
                profitERP P (Function.update p 1 x) 1 ≤ profitERP P p 1 ↔
                (x - P.c) * D A1 A0 (p 0) (p 1) ≤ (p 1 - P.c) * D A1 A0 (p 0) x := by
              intro p x
              have hp : profitERP P p 1 = profitERP P (Function.update p 1 (p 1)) 1 := by
                rw [Function.update_eq_self]
              have k : 0 < P.m * A1 := mul_pos hm hA1p
              rw [hp, H1 p x, H1 p (p 1), div_le_div_iff₀ (Dpos _ _ _ _ hA1p hA0p.le) (Dpos _ _ _ _ hA1p hA0p.le),
                show P.m * (x - P.c) * A1 * D A1 A0 (p 0) (p 1) = (P.m * A1) * ((x - P.c) * D A1 A0 (p 0) (p 1)) by ring,
                show P.m * (p 1 - P.c) * A1 * D A1 A0 (p 0) x = (P.m * A1) * ((p 1 - P.c) * D A1 A0 (p 0) x) by ring]
              exact mul_le_mul_iff_of_pos_left k
            have EQ : ∀ p : Fin 2 → ℝ, IsEqERP P p ↔ Cond A0 A1 (p 1) (p 0) ∧ Cond A1 A0 (p 0) (p 1) := by
              intro p
              rw [← KEY A0 A1 (p 1) (p 0) hA0p hA1p, ← KEY A1 A0 (p 0) (p 1) hA1p hA0p]
              simp only [IsEqERP, CarbonDoubleCount.Planner.IsPureNash, Set.mem_univ, forall_const,
                true_and, Fin.forall_fin_two, PR0, PR1]
            have SYM : ∀ t, Cond A0 A1 t t ∧ Cond A1 A0 t t ↔
                (P.γ * A1 * (t - P.c) ≤ e + A0 + A1 ∧ e + A0 + A1 ≤ P.γ * (e + A0) * (t - P.c)) := by
              intro t
              simp only [hCond, lt_self_iff_false, false_and, or_false, false_or, true_and]
              constructor
              · rintro ⟨⟨h1, _⟩, _, h4⟩
                exact ⟨h1, by linarith only [h4]⟩
              · rintro ⟨h1, h2⟩
                have hv : 0 < t - P.c := by
                  have : 0 < P.γ * (e + A0) * (t - P.c) := by linarith only [h2, he0, hA0p, hA1p]
                  exact pos_of_mul_pos_right this (by positivity)
                have k1 : P.γ * (e + A0) * (t - P.c) ≤ P.γ * (e + A1) * (t - P.c) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [hA01]) hγ.le) hv.le
                have k2 : P.γ * A0 * (t - P.c) ≤ P.γ * A1 * (t - P.c) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA01 hγ.le) hv.le
                exact ⟨⟨h1, by linarith only [h2, k1]⟩, by linarith only [h1, k2], by linarith only [h2]⟩
            have INT : ∀ t, t ∈ Set.Icc L U ↔
                (P.γ * A1 * (t - P.c) ≤ e + A0 + A1 ∧ e + A0 + A1 ≤ P.γ * (e + A0) * (t - P.c)) := by
              intro t
              rw [Set.mem_Icc, hL, hU]
              have k1 : 0 < P.γ * (e + A0) := by positivity
              have k2 : 0 < P.γ * A1 := by positivity
              constructor
              · rintro ⟨h1, h2⟩
                have h1' : (e + A0 + A1) / (P.γ * (e + A0)) ≤ t - P.c := by linarith only [h1]
                have h2' : t - P.c ≤ (e + A0 + A1) / (P.γ * A1) := by linarith only [h2]
                rw [div_le_iff₀ k1] at h1'
                rw [le_div_iff₀ k2] at h2'
                exact ⟨by linarith only [h2'], by linarith only [h1']⟩
              · rintro ⟨h1, h2⟩
                have h1' : (e + A0 + A1) / (P.γ * (e + A0)) ≤ t - P.c := by
                  rw [div_le_iff₀ k1]; linarith only [h2]
                have h2' : t - P.c ≤ (e + A0 + A1) / (P.γ * A1) := by
                  rw [le_div_iff₀ k2]; linarith only [h1]
                exact ⟨by linarith only [h1'], by linarith only [h2']⟩
            have ALG : ∀ G w v0 v1 : ℝ, 0 < G → v0 < v1 → w = G * (P.γ * v1 - 1) →
                G + w = P.γ * v0 * w → 0 < w → G < w := by
              intro G w v0 v1 hG hv hw h2 hwp
              have hs : 0 < P.γ * v1 - 1 := pos_of_mul_pos_right (hw ▸ hwp) hG.le
              have h3 : G * (1 + (P.γ * v1 - 1)) = G * (P.γ * v0 * (P.γ * v1 - 1)) := by
                linear_combination h2 - (1 - P.γ * v0) * hw
              have h4 := mul_left_cancel₀ hG.ne' h3
              have h5 : P.γ * v0 * (P.γ * v1 - 1) < (1 + (P.γ * v1 - 1)) * (P.γ * v1 - 1) :=
                mul_lt_mul_of_pos_right (by linarith only [mul_lt_mul_of_pos_left hv hγ]) hs
              have h6 : 0 < (1 + (P.γ * v1 - 1)) * ((P.γ * v1 - 1) - 1) := by linarith only [h4, h5]
              have h7 : 1 < P.γ * v1 - 1 := by linarith only [pos_of_mul_pos_right h6 (by linarith only [hs])]
              rw [hw]; exact lt_mul_of_one_lt_right hG h7
            have LTC : ∀ p : Fin 2 → ℝ, IsEqERP P p → p 0 < p 1 →
                A1 * Real.exp (P.γ * (p 0 - p 1)) = (e + A0) * (P.γ * (p 1 - P.c) - 1) ∧
                e + A0 + A1 * Real.exp (P.γ * (p 0 - p 1)) =
                  P.γ * (p 0 - P.c) * (A1 * Real.exp (P.γ * (p 0 - p 1))) := by
              intro p hp hlt
              rw [EQ, hCond, hCond] at hp
              obtain ⟨h0, h1⟩ := hp
              have h0' : e + A0 + A1 * Real.exp (P.γ * (p 0 - p 1)) =
                  P.γ * (p 0 - P.c) * (A1 * Real.exp (P.γ * (p 0 - p 1))) := by
                rcases h0 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
                · exact h
                · exact absurd h hlt.ne
                · exact absurd h (not_lt.mpr hlt.le)
              have h1' : A1 + (e + A0) * Real.exp (P.γ * (p 1 - p 0)) =
                  P.γ * (p 1 - P.c) * ((e + A0) * Real.exp (P.γ * (p 1 - p 0))) := by
                rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
                · exact absurd h (not_lt.mpr hlt.le)
                · exact absurd h hlt.ne'
                · exact h
              have hg : Real.exp (P.γ * (p 1 - p 0)) * Real.exp (P.γ * (p 0 - p 1)) = 1 := by
                rw [← Real.exp_add, show P.γ * (p 1 - p 0) + P.γ * (p 0 - p 1) = 0 by ring, Real.exp_zero]
              refine ⟨?_, h0'⟩
              linear_combination (Real.exp (P.γ * (p 0 - p 1))) * h1' +
                (P.γ * (p 1 - P.c) * (e + A0) - (e + A0)) * hg
            have NOGT : ∀ p : Fin 2 → ℝ, IsEqERP P p → ¬ p 1 < p 0 := by
              intro p hp hlt
              rw [EQ, hCond, hCond] at hp
              obtain ⟨h0, h1⟩ := hp
              have h0' : A0 + (e + A1) * Real.exp (P.γ * (p 0 - p 1)) =
                  P.γ * (p 0 - P.c) * ((e + A1) * Real.exp (P.γ * (p 0 - p 1))) := by
                rcases h0 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
                · exact absurd h (not_lt.mpr hlt.le)
                · exact absurd h hlt.ne'
                · exact h
              have h1' : e + A1 + A0 * Real.exp (P.γ * (p 1 - p 0)) =
                  P.γ * (p 1 - P.c) * (A0 * Real.exp (P.γ * (p 1 - p 0))) := by
                rcases h1 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
                · exact h
                · exact absurd h hlt.ne
                · exact absurd h (not_lt.mpr hlt.le)
              have hg : Real.exp (P.γ * (p 0 - p 1)) * Real.exp (P.γ * (p 1 - p 0)) = 1 := by
                rw [← Real.exp_add, show P.γ * (p 0 - p 1) + P.γ * (p 1 - p 0) = 0 by ring, Real.exp_zero]
              have hw : A0 * Real.exp (P.γ * (p 1 - p 0)) = (e + A1) * (P.γ * (p 0 - P.c) - 1) := by
                linear_combination (Real.exp (P.γ * (p 1 - p 0))) * h0' +
                  (P.γ * (p 0 - P.c) * (e + A1) - (e + A1)) * hg
              have hh : Real.exp (P.γ * (p 1 - p 0)) < 1 :=
                (Real.exp_lt_exp.mpr (mul_neg_of_pos_of_neg hγ (by linarith only [hlt]))).trans_eq Real.exp_zero
              have := ALG (e + A1) (A0 * Real.exp (P.γ * (p 1 - p 0))) (p 1 - P.c) (p 0 - P.c)
                (by positivity) (by linarith only [hlt]) hw h1' (by positivity)
              have : A0 * Real.exp (P.γ * (p 1 - p 0)) < A0 := mul_lt_of_lt_one_right hA0p hh
              linarith only [this, ‹e + A1 < _›, hA01, he0]
            have NOLT : A1 ≤ e + A0 → ∀ p : Fin 2 → ℝ, IsEqERP P p → ¬ p 0 < p 1 := by
              intro hEB p hp hlt
              obtain ⟨hw, h2⟩ := LTC p hp hlt
              have hh : Real.exp (P.γ * (p 0 - p 1)) < 1 :=
                (Real.exp_lt_exp.mpr (mul_neg_of_pos_of_neg hγ (by linarith only [hlt]))).trans_eq Real.exp_zero
              have := ALG (e + A0) (A1 * Real.exp (P.γ * (p 0 - p 1))) (p 0 - P.c) (p 1 - P.c)
                (by positivity) (by linarith only [hlt]) hw h2 (by positivity)
              have : A1 * Real.exp (P.γ * (p 0 - p 1)) < A1 := mul_lt_of_lt_one_right hA1p hh
              linarith only [this, ‹e + A0 < _›, hEB]
            have PART1 : A1 ≤ e + A0 → ∀ p : Fin 2 → ℝ, IsEqERP P p ↔ p 0 = p 1 ∧ p 0 ∈ Set.Icc L U := by
              intro hEB p
              constructor
              · intro hp
                have h01 : p 0 = p 1 := by
                  rcases lt_trichotomy (p 0) (p 1) with h | h | h
                  · exact absurd h (NOLT hEB p hp)
                  · exact h
                  · exact absurd h (NOGT p hp)
                refine ⟨h01, (INT _).mpr ((SYM _).mp ?_)⟩
                rw [EQ, ← h01] at hp; exact hp
              · rintro ⟨h01, hI⟩
                rw [EQ, ← h01]; exact (SYM _).mpr ((INT _).mp hI)
            have hX : ∀ q : Fin 2 → ℝ, Real.exp (P.a 1 - P.γ * (q 1 - q 0 + P.ct)) =
                A1 * Real.exp (P.γ * (q 0 - q 1)) := by
              intro q; rw [hA1, ← Real.exp_add]; congr 1; ring
            have SOLU : ∀ s t : ℝ, 0 < s → 0 < t → A1 * Real.exp (1 / s - s) = (e + A0) * s →
                A1 * Real.exp (1 / t - t) = (e + A0) * t → s = t := by
              intro s t hs ht h1 h2
              have key : ∀ s t : ℝ, 0 < s → s < t → A1 * Real.exp (1 / s - s) = (e + A0) * s →
                  A1 * Real.exp (1 / t - t) = (e + A0) * t → False := by
                intro s t hs hst h1 h2
                have k1 : 1 / t - t < 1 / s - s := by
                  have := one_div_lt_one_div_of_lt hs hst
                  linarith only [this, hst]
                have k2 := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr k1) hA1p
                have k3 := mul_lt_mul_of_pos_left hst hBp
                linarith only [k2, k3, h1, h2]
              rcases lt_trichotomy s t with h | h | h
              · exact (key s t hs h h1 h2).elim
              · exact h
              · exact (key t s ht h h2 h1).elim
            have UNIQ : ∀ p q : Fin 2 → ℝ,
                (A1 * Real.exp (P.γ * (p 0 - p 1)) = (e + A0) * (P.γ * (p 1 - P.c) - 1) ∧
                  P.γ * (p 0 - P.c) - 1 = 1 / (P.γ * (p 1 - P.c) - 1)) →
                (A1 * Real.exp (P.γ * (q 0 - q 1)) = (e + A0) * (P.γ * (q 1 - P.c) - 1) ∧
                  P.γ * (q 0 - P.c) - 1 = 1 / (P.γ * (q 1 - P.c) - 1)) → q = p := by
              intro p q ⟨hp1, hp2⟩ ⟨hq1, hq2⟩
              have spos : ∀ r : Fin 2 → ℝ, A1 * Real.exp (P.γ * (r 0 - r 1)) =
                  (e + A0) * (P.γ * (r 1 - P.c) - 1) → 0 < P.γ * (r 1 - P.c) - 1 := by
                intro r hr
                exact pos_of_mul_pos_right (hr ▸ (by positivity : 0 < A1 * Real.exp (P.γ * (r 0 - r 1)))) hBp.le
              have conv : ∀ r : Fin 2 → ℝ, P.γ * (r 0 - P.c) - 1 = 1 / (P.γ * (r 1 - P.c) - 1) →
                  P.γ * (r 0 - r 1) = 1 / (P.γ * (r 1 - P.c) - 1) - (P.γ * (r 1 - P.c) - 1) := by
                intro r hr; rw [← hr]; ring
              have hs := SOLU _ _ (spos p hp1) (spos q hq1) (by rw [← conv p hp2]; exact hp1)
                (by rw [← conv q hq2]; exact hq1)
              have e1 : q 1 = p 1 := by
                have : P.γ * (q 1 - p 1) = 0 := by linear_combination -hs
                have := (mul_eq_zero.mp this).resolve_left hγ.ne'
                linarith only [this]
              have e0 : q 0 = p 0 := by
                have h' : P.γ * (q 0 - P.c) - 1 = P.γ * (p 0 - P.c) - 1 := by rw [hq2, hp2, e1]
                have : P.γ * (q 0 - p 0) = 0 := by linear_combination h'
                have := (mul_eq_zero.mp this).resolve_left hγ.ne'
                linarith only [this]
              funext i; fin_cases i
              · exact e0
              · exact e1
            have CHAR : e + A0 < A1 → ∀ p : Fin 2 → ℝ, IsEqERP P p → p 0 < p 1 ∧
                (A1 * Real.exp (P.γ * (p 0 - p 1)) = (e + A0) * (P.γ * (p 1 - P.c) - 1) ∧
                  P.γ * (p 0 - P.c) - 1 = 1 / (P.γ * (p 1 - P.c) - 1)) := by
              intro hBE p hp
              have hlt : p 0 < p 1 := by
                rcases lt_trichotomy (p 0) (p 1) with h | h | h
                · exact h
                · exfalso
                  have hp' := hp
                  rw [EQ, ← h] at hp'
                  obtain ⟨k1, k2⟩ := (SYM _).mp hp'
                  have hv : 0 < p 0 - P.c := by
                    have : 0 < P.γ * (e + A0) * (p 0 - P.c) := by linarith only [k2, he0, hA0p, hA1p]
                    exact pos_of_mul_pos_right this (by positivity)
                  have k3 : P.γ * (e + A0) * (p 0 - P.c) < P.γ * A1 * (p 0 - P.c) :=
                    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hBE hγ) hv
                  linarith only [k1, k2, k3]
                · exact absurd h (NOGT p hp)
              obtain ⟨hw, h2⟩ := LTC p hp hlt
              refine ⟨hlt, hw, ?_⟩
              have hs : 0 < P.γ * (p 1 - P.c) - 1 :=
                pos_of_mul_pos_right (hw ▸ (by positivity : 0 < A1 * Real.exp (P.γ * (p 0 - p 1)))) hBp.le
              rw [eq_div_iff hs.ne']
              have : (e + A0) * ((P.γ * (p 0 - P.c) - 1) * (P.γ * (p 1 - P.c) - 1) - 1) = 0 := by
                linear_combination (-1 : ℝ) * h2 - (P.γ * (p 0 - P.c) - 1) * hw
              have := (mul_eq_zero.mp this).resolve_left hBp.ne'
              linarith only [this]
            refine ⟨PART1, ?_, ?_, ?_⟩
            · intro hBE
              have hLU : L < U := by
                rw [hL, hU]
                have : (e + A0 + A1) / (P.γ * (e + A0)) < (e + A0 + A1) / (P.γ * A1) :=
                  div_lt_div_of_pos_left (by positivity) (by positivity)
                    (mul_lt_mul_of_pos_left hBE hγ)
                linarith only [this]
              have hinf := (Set.Icc_infinite hLU).image (f := fun t : ℝ => (fun _ : Fin 2 => t))
                (fun a _ b _ hab => congrFun hab 0)
              refine hinf.mono ?_
              rintro _ ⟨t, ht, rfl⟩
              exact (PART1 hBE.le _).mpr ⟨rfl, ht⟩
            · intro hBE
              refine ⟨fun _ => L, (PART1 hBE.le _).mpr ⟨rfl, ?_⟩, ?_⟩
              · rw [Set.mem_Icc]; exact ⟨le_rfl, by rw [hL, hU, hBE]⟩
              · intro q hq
                obtain ⟨h01, hI⟩ := (PART1 hBE.le q).mp hq
                have hLU : U = L := by rw [hL, hU, hBE]
                rw [hLU] at hI
                have hq0 : q 0 = L := le_antisymm hI.2 hI.1
                funext i; fin_cases i
                · exact hq0
                · exact h01 ▸ hq0
            · intro hBE
              -- existence via IVT
              have hcont : ContinuousOn (fun s : ℝ => (e + A0) * s * Real.exp (s - 1 / s))
                  (Set.Icc 1 (A1 / (e + A0))) := by
                apply ContinuousOn.mul (by fun_prop)
                apply Real.continuous_exp.comp_continuousOn
                apply ContinuousOn.sub continuousOn_id
                apply ContinuousOn.div continuousOn_const continuousOn_id
                intro x hx; have := hx.1; exact (show (0:ℝ) < x by linarith only [this]).ne'
              have hb1 : 1 ≤ A1 / (e + A0) := by rw [le_div_iff₀ hBp]; linarith only [hBE]
              have hmem : A1 ∈ Set.Icc ((e + A0) * 1 * Real.exp (1 - 1 / 1))
                  ((e + A0) * (A1 / (e + A0)) * Real.exp (A1 / (e + A0) - 1 / (A1 / (e + A0)))) := by
                constructor
                · norm_num; exact hBE.le
                · rw [mul_div_cancel₀ _ hBp.ne']
                  have : 0 ≤ A1 / (e + A0) - 1 / (A1 / (e + A0)) := by
                    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hb1
                    linarith only [this, hb1]
                  exact le_mul_of_one_le_right hA1p.le (Real.one_le_exp this)
              obtain ⟨s, hsI, hg⟩ := intermediate_value_Icc hb1 hcont hmem
              simp only at hg
              have hs1 : 1 < s := by
                rcases eq_or_lt_of_le hsI.1 with h | h
                · exfalso; rw [← h] at hg; norm_num at hg; linarith only [hg, hBE]
                · exact h
              have hs0 : 0 < s := by linarith only [hs1]
              have hprod : Real.exp (s - 1 / s) * Real.exp (1 / s - s) = 1 := by
                rw [← Real.exp_add, show s - 1 / s + (1 / s - s) = 0 by ring, Real.exp_zero]
              have hZ : A1 * Real.exp (1 / s - s) = (e + A0) * s := by
                linear_combination (-Real.exp (1 / s - s)) * hg + ((e + A0) * s) * hprod
              obtain ⟨p, hp0, hp1⟩ : ∃ p : Fin 2 → ℝ, p 0 = P.c + (1 / s + 1) / P.γ ∧
                  p 1 = P.c + (s + 1) / P.γ := ⟨![_, _], rfl, rfl⟩
              have gp0 : P.γ * (p 0 - P.c) = 1 / s + 1 := by rw [hp0]; field_simp; ring
              have gp1 : P.γ * (p 1 - P.c) = s + 1 := by rw [hp1]; field_simp; ring
              have g01 : P.γ * (p 0 - p 1) = 1 / s - s := by linear_combination gp0 - gp1
              have g10 : P.γ * (p 1 - p 0) = s - 1 / s := by linear_combination gp1 - gp0
              have hlt : p 0 < p 1 := by
                have : P.γ * (p 0 - p 1) < 0 := by
                  rw [g01]; have := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 1) hs1
                  linarith only [this, hs1]
                have := (neg_of_mul_neg_right this hγ.le)
                linarith only [this]
              have hpeq : IsEqERP P p := by
                rw [EQ, hCond, hCond]
                constructor
                · left; refine ⟨hlt, ?_⟩
                  rw [g01, gp0, hZ]; field_simp
                · right; right; refine ⟨hlt, ?_⟩
                  rw [g10, gp1]
                  linear_combination (-1 : ℝ) * hg
              have sysp : A1 * Real.exp (P.γ * (p 0 - p 1)) = (e + A0) * (P.γ * (p 1 - P.c) - 1) ∧
                  P.γ * (p 0 - P.c) - 1 = 1 / (P.γ * (p 1 - P.c) - 1) := by
                constructor
                · rw [g01, gp1, hZ]; ring
                · rw [gp0, gp1]; ring
              refine ⟨⟨p, hpeq, fun q hq => UNIQ p q sysp (CHAR hBE q hq).2⟩, ?_⟩
              intro r hr
              obtain ⟨hlt', h1, h2⟩ := CHAR hBE r hr
              refine ⟨hlt', by rw [hX r]; exact h1, h2, ?_⟩
              intro q hq1 hq2
              rw [hX q] at hq1
              exact UNIQ r q ⟨h1, h2⟩ ⟨hq1, hq2⟩
