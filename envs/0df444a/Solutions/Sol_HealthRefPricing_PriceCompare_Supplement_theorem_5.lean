-- Prove2me | solution 1 for HealthRefPricing.PriceCompare.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:24.721585+00:00
-- url     : https://prove2.me/submissions/5e40db74-0410-43ab-a4a9-050753df1cce

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Supplement_Assumption5

open HealthRefPricing
open HealthRefPricing.PriceCompare
open HealthRefPricing.PriceCompare.Supplement

/-- Theorem 5: existence, system (11), and uniqueness for the equilibrium's given status set.
Auxiliary prices for value-based providers are existential witnesses, not game strategies. -/
theorem solution (P : Params) (hS : P.Standing) (lam : ℝ)
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) (hA5 : Assumption5 P lam) :
    (∃ p : Fin 2 → ℝ, IsEqRV P lam p) ∧
    ∀ p : Fin 2 → ℝ, IsEqRV P lam p →
      (∀ j : Fin 2, P.ps < p j →
        1 - P.γ * (p j - P.c) * (1 - share P (oopRV P lam p) j) = 0) ∧
      (∀ j : Fin 2, p j ≤ P.ps → ∃ phat : ℝ,
        1 - P.γ * lam * (phat - P.c) *
          (1 - share P (oopRV P lam (vs j phat (p (1 - j)))) j) = 0 ∧
        p j = min phat P.ps) ∧
      (∀ q : Fin 2 → ℝ,
        (∀ j : Fin 2, P.ps < p j → P.ps < q j ∧
          1 - P.γ * (q j - P.c) * (1 - share P (oopRV P lam q) j) = 0) →
        (∀ j : Fin 2, p j ≤ P.ps → ∃ qhat : ℝ,
          1 - P.γ * lam * (qhat - P.c) *
            (1 - share P (oopRV P lam (vs j qhat (q (1 - j)))) j) = 0 ∧
          q j = min qhat P.ps) → q = p) := by
            obtain ⟨hm, hγ, hc, ha, hct⟩ := hS
            obtain ⟨hl0, hl1⟩ := hlam
            obtain ⟨o, ho⟩ : ∃ o : ℝ → ℝ, o = fun x => lam * min x P.ps + max 0 (x - P.ps) := ⟨_, rfl⟩
            have hshare : ∀ (j : Fin 2) (x y : ℝ), share P (oopRV P lam (vs j x y)) j =
                Real.exp (P.a j - P.γ * o x) / ((Real.exp P.u0 + Real.exp (P.a (1 - j) - P.γ * o y))
                  + Real.exp (P.a j - P.γ * o x)) := by
              intro j x y
              subst ho
              fin_cases j <;> simp [share, oopRV, vs, Fin.sum_univ_two, Function.update] <;> ring
            have hprofit : ∀ (j : Fin 2) (x y : ℝ), profitRV P lam (vs j x y) j =
                P.m * (x - P.c) * share P (oopRV P lam (vs j x y)) j := by
              intro j x y; simp [profitRV, vs]
            have hupd : ∀ (j : Fin 2) (p : Fin 2 → ℝ) (x : ℝ), Function.update p j x = vs j x (p (1 - j)) := by
              intro j p x
              funext i
              fin_cases j <;> fin_cases i <;> simp [vs, Function.update]
            have hself : ∀ (j : Fin 2) (p : Fin 2 → ℝ), p = vs j (p j) (p (1 - j)) := by
              intro j p
              rw [← hupd]; simp
            have hvs0 : ∀ b y x : ℝ, Function.update (vs 0 b y) 0 x = vs 0 x y := by
              intro b y x; funext i; fin_cases i <;> simp [vs, Function.update]
            have hvs1 : ∀ b y x : ℝ, Function.update (vs 0 b y) 1 x = vs 1 x b := by
              intro b y x; funext i; fin_cases i <;> simp [vs, Function.update]
            have hvs01 : ∀ b y : ℝ, vs 0 b y = vs 1 y b := by
              intro b y; funext i; fin_cases i <;> simp [vs, Function.update]
            have hoc : Continuous o := by
              subst ho
              exact (continuous_const.mul (continuous_id.min continuous_const)).add
                (continuous_const.max (continuous_id.sub continuous_const))
            have homono : ∀ x y, x < y → o x < o y := by
              intro x y hxy
              subst ho
              simp only
              rcases le_total x P.ps with h1 | h1 <;> rcases le_total y P.ps with h2 | h2
              · rw [min_eq_left h1, min_eq_left h2, max_eq_left (by linarith), max_eq_left (by linarith)]
                nlinarith
              · rw [min_eq_left h1, min_eq_right h2, max_eq_left (by linarith), max_eq_right (by linarith)]
                nlinarith
              · linarith
              · rw [min_eq_right h1, min_eq_right h2, max_eq_right (by linarith), max_eq_right (by linarith)]
                linarith
            have hderiv : ∀ A N s b x : ℝ, 0 < N →
                HasDerivAt (fun x => P.m * (x - P.c) * (Real.exp (A - P.γ * (s * x + b)) /
                    (N + Real.exp (A - P.γ * (s * x + b)))))
                  (P.m * (Real.exp (A - P.γ * (s * x + b)) / (N + Real.exp (A - P.γ * (s * x + b)))) *
                    (1 - P.γ * s * (x - P.c) * (N / (N + Real.exp (A - P.γ * (s * x + b)))))) x := by
              intro A N s b x hN
              have h1 : HasDerivAt (fun x => A - P.γ * (s * x + b)) (-(P.γ * s)) x := by
                have := (((hasDerivAt_id x).const_mul s).add_const b).const_mul P.γ |>.const_sub A
                simpa using this
              have hE := h1.exp
              have hD := hE.const_add N
              have hpos : 0 < N + Real.exp (A - P.γ * (s * x + b)) := by positivity
              have hq := hE.div hD hpos.ne'
              have hlin := ((hasDerivAt_id x).sub_const P.c).const_mul P.m
              have := hlin.mul hq
              refine this.congr_deriv ?_
              simp only [Pi.div_apply, id]
              field_simp
              ring
            have hFOC : ∀ A N x0 : ℝ, 0 < N →
                (∀ x, P.m * (x - P.c) * (Real.exp (A - P.γ * o x) / (N + Real.exp (A - P.γ * o x))) ≤
                  P.m * (x0 - P.c) * (Real.exp (A - P.γ * o x0) / (N + Real.exp (A - P.γ * o x0)))) →
                (P.ps < x0 → 1 - P.γ * (x0 - P.c) *
                    (1 - Real.exp (A - P.γ * o x0) / (N + Real.exp (A - P.γ * o x0))) = 0) ∧
                (x0 ≤ P.ps → ∃ xh, 1 - P.γ * lam * (xh - P.c) *
                    (1 - Real.exp (A - P.γ * o xh) / (N + Real.exp (A - P.γ * o xh))) = 0 ∧
                    x0 = min xh P.ps) := by
              intro A N x0 hN hmax
              have hoHi : ∀ x, P.ps ≤ x → o x = 1 * x + (lam * P.ps - P.ps) := by
                intro x hx; subst ho; simp only; rw [min_eq_right hx, max_eq_right (by linarith)]; try ring
              have hoLo : ∀ x, x ≤ P.ps → o x = lam * x + 0 := by
                intro x hx; subst ho; simp only; rw [min_eq_left hx, max_eq_left (by linarith)]; try ring
              have hone : ∀ E : ℝ, 0 ≤ E → 1 - E / (N + E) = N / (N + E) := by
                intro E hE; field_simp; ring
              have hSpos : ∀ y, 0 < Real.exp (A - P.γ * y) / (N + Real.exp (A - P.γ * y)) :=
                fun y => by positivity
              constructor
              · intro hx0
                have hd := hderiv A N 1 (lam * P.ps - P.ps) x0 hN
                have hloc : IsLocalMax (fun x => P.m * (x - P.c) *
                    (Real.exp (A - P.γ * (1 * x + (lam * P.ps - P.ps))) /
                    (N + Real.exp (A - P.γ * (1 * x + (lam * P.ps - P.ps)))))) x0 := by
                  filter_upwards [Ioi_mem_nhds hx0] with x hx
                  rw [← hoHi x (le_of_lt hx), ← hoHi x0 hx0.le]
                  exact hmax x
                have h0 := hloc.hasDerivAt_eq_zero hd
                rw [← hoHi x0 hx0.le] at h0
                rw [hone _ (Real.exp_pos _).le]
                have := hSpos (o x0)
                have h2 : 1 - P.γ * 1 * (x0 - P.c) * (N / (N + Real.exp (A - P.γ * o x0))) = 0 := by
                  rcases mul_eq_zero.mp h0 with h | h
                  · exfalso; have := mul_pos hm this; linarith
                  · exact h
                simpa using h2
              · intro hx0
                rcases lt_or_eq_of_le hx0 with hlt | heq
                · refine ⟨x0, ?_, (min_eq_left hx0).symm⟩
                  have hd := hderiv A N lam 0 x0 hN
                  have hloc : IsLocalMax (fun x => P.m * (x - P.c) * (Real.exp (A - P.γ * (lam * x + 0)) /
                      (N + Real.exp (A - P.γ * (lam * x + 0))))) x0 := by
                    filter_upwards [Iio_mem_nhds hlt] with x hx
                    rw [← hoLo x (le_of_lt hx), ← hoLo x0 hx0]
                    exact hmax x
                  have h0 := hloc.hasDerivAt_eq_zero hd
                  rw [← hoLo x0 hx0] at h0
                  rw [hone _ (Real.exp_pos _).le]
                  have := hSpos (o x0)
                  rcases mul_eq_zero.mp h0 with h | h
                  · exfalso; have := mul_pos hm this; linarith
                  · linarith [h]
                · 
                  have hd := hderiv A N lam 0 x0 hN
                  have hclaim : 0 ≤ 1 - P.γ * lam * (x0 - P.c) *
                      (N / (N + Real.exp (A - P.γ * (lam * x0 + 0)))) := by
                    by_contra hneg
                    push Not at hneg
                    have hdneg := mul_neg_of_pos_of_neg (mul_pos hm (hSpos (lam * x0 + 0))) hneg
                    have hev := (hd.hasDerivWithinAt (s := Set.Iio x0)).limsup_slope_le hdneg
                    rw [Set.sdiff_singleton_eq_self (by simp)] at hev
                    obtain ⟨z, hz1, hz2⟩ := (hev.and self_mem_nhdsWithin).exists
                    rw [slope_def_field] at hz1
                    have hz2' : z < x0 := hz2
                    have hle := hmax z
                    rw [hoLo z (by linarith), hoLo x0 hx0] at hle
                    have : 0 < z - x0 → False := fun h => by linarith
                    rw [div_neg_iff] at hz1
                    rcases hz1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                    · linarith
                    · linarith
                  set Eps := Real.exp (A - P.γ * o x0) with hEps
                  have hφps : 0 ≤ 1 - P.γ * lam * (x0 - P.c) * (1 - Eps / (N + Eps)) := by
                    rw [hone _ (Real.exp_pos _).le, hoLo x0 hx0]; exact hclaim
                  have hK : 0 < P.γ * lam := mul_pos hγ hl0
                  set Mx := max x0 P.c + (N + Eps) / (P.γ * lam * N) with hMx
                  have hq0 : 0 < (N + Eps) / (P.γ * lam * N) := by positivity
                  have hMx1 : x0 ≤ Mx := by have := le_max_left x0 P.c; linarith
                  have hMx2 : (N + Eps) / (P.γ * lam * N) ≤ Mx - P.c := by
                    have := le_max_right x0 P.c; linarith
                  have hEle : Real.exp (A - P.γ * o Mx) ≤ Eps := by
                    rw [hEps]; apply Real.exp_le_exp.mpr
                    rw [hoHi Mx (by linarith), hoHi x0 heq.ge]; nlinarith
                  have hφM : 1 - P.γ * lam * (Mx - P.c) *
                      (1 - Real.exp (A - P.γ * o Mx) / (N + Real.exp (A - P.γ * o Mx))) ≤ 0 := by
                    rw [hone _ (Real.exp_pos _).le]
                    have h1 : N / (N + Eps) ≤ N / (N + Real.exp (A - P.γ * o Mx)) :=
                      div_le_div_of_nonneg_left hN.le (by positivity) (by linarith)
                    have h3 : P.γ * lam * ((N + Eps) / (P.γ * lam * N)) * (N / (N + Eps)) = 1 := by
                      have : 0 < N + Eps := by positivity
                      field_simp
                    have := mul_le_mul (mul_le_mul_of_nonneg_left hMx2 hK.le) h1 (by positivity)
                      (by nlinarith)
                    linarith
                  have hcont : ContinuousOn (fun x => 1 - P.γ * lam * (x - P.c) *
                      (1 - Real.exp (A - P.γ * o x) / (N + Real.exp (A - P.γ * o x)))) (Set.Icc x0 Mx) := by
                    apply Continuous.continuousOn
                    have hEc : Continuous (fun x => Real.exp (A - P.γ * o x)) :=
                      Real.continuous_exp.comp (continuous_const.sub (continuous_const.mul hoc))
                    exact continuous_const.sub ((continuous_const.mul (continuous_id.sub continuous_const)).mul
                      (continuous_const.sub (hEc.div (continuous_const.add hEc) (fun x => by positivity))))
                  obtain ⟨xh, ⟨hxh1, hxh2⟩, hφ⟩ := intermediate_value_Icc' hMx1 hcont ⟨hφM, hφps⟩
                  exact ⟨xh, hφ, by rw [min_eq_right (by linarith)]; exact heq⟩
            obtain ⟨G, hG⟩ : ∃ G : Fin 2 → ℝ → ℝ, G = fun k z => Real.exp (P.a k - P.γ * o z) := ⟨_, rfl⟩
            have hGpos : ∀ k z, 0 < G k z := by intro k z; rw [hG]; positivity
            have hGanti : ∀ k z z', z < z' → G k z' < G k z := by
              intro k z z' h; rw [hG]; simp only
              apply Real.exp_lt_exp.mpr; have := homono z z' h; nlinarith
            have hGanti' : ∀ k z z', z ≤ z' → G k z' ≤ G k z := by
              intro k z z' h; rcases eq_or_lt_of_le h with h | h
              · rw [h]
              · exact (hGanti k z z' h).le
            have hGkey : ∀ k z w z' w', o z + o w ≤ o z' + o w' → G k z' * G k w' ≤ G k z * G k w := by
              intro k z w z' w' h; rw [hG]; simp only; rw [← Real.exp_add, ← Real.exp_add]
              apply Real.exp_le_exp.mpr; nlinarith
            set U := Real.exp P.u0 with hU
            have hUpos : 0 < U := Real.exp_pos _
            have hsh : ∀ (j : Fin 2) (x y : ℝ), share P (oopRV P lam (vs j x y)) j =
                G j x / ((U + G (1 - j) y) + G j x) := by
              intro j x y; rw [hshare, hG]
            have hsp : ∀ (j : Fin 2) (p : Fin 2 → ℝ), share P (oopRV P lam p) j =
                G j (p j) / ((U + G (1 - j) (p (1 - j))) + G j (p j)) := by
              intro j p; have := hsh j (p j) (p (1 - j)); rwa [← hself j p] at this
            have hBR : ∀ (j : Fin 2) (y x : ℝ),
                (∀ x', profitRV P lam (vs j x' y) j ≤ profitRV P lam (vs j x y) j) →
                (P.ps < x → 1 - P.γ * (x - P.c) * (1 - share P (oopRV P lam (vs j x y)) j) = 0) ∧
                (x ≤ P.ps → ∃ xh, 1 - P.γ * lam * (xh - P.c) *
                  (1 - share P (oopRV P lam (vs j xh y)) j) = 0 ∧ x = min xh P.ps) := by
              intro j y x h
              have hN : 0 < Real.exp P.u0 + Real.exp (P.a (1 - j) - P.γ * o y) := by positivity
              have := hFOC (P.a j) _ x hN (fun x' => by
                have := h x'; rwa [hprofit, hprofit, hshare, hshare] at this)
              simpa only [hshare] using this
            have hpart2 : ∀ p : Fin 2 → ℝ, IsEqRV P lam p →
                (∀ j : Fin 2, P.ps < p j →
                  1 - P.γ * (p j - P.c) * (1 - share P (oopRV P lam p) j) = 0) ∧
                (∀ j : Fin 2, p j ≤ P.ps → ∃ phat : ℝ,
                  1 - P.γ * lam * (phat - P.c) *
                    (1 - share P (oopRV P lam (vs j phat (p (1 - j)))) j) = 0 ∧
                  p j = min phat P.ps) := by
              intro p hp
              have hb : ∀ j : Fin 2, ∀ x', profitRV P lam (vs j x' (p (1 - j))) j ≤
                  profitRV P lam (vs j (p j) (p (1 - j))) j := by
                intro j x'
                have h := hp.2 j x' (Set.mem_univ _)
                rw [hupd] at h
                rwa [← hself j p]
              refine ⟨fun j hj => ?_, fun j hj => (hBR j _ _ (hb j)).2 hj⟩
              have := (hBR j _ _ (hb j)).1 hj
              rwa [← hself j p] at this
            have h11 : ∀ j : Fin 2, 1 - (1 - j) = j := by intro j; fin_cases j <;> rfl
            have hstepA : ∀ (gk xk xk' N N' : ℝ) (k : Fin 2), 0 < gk → 0 < N → 0 < N' → xk < xk' →
                1 - P.γ * gk * (xk - P.c) * (1 - G k xk / (N + G k xk)) = 0 →
                1 - P.γ * gk * (xk' - P.c) * (1 - G k xk' / (N' + G k xk')) = 0 →
                N' * G k xk < N * G k xk' := by
              intro gk xk xk' N N' k hg hN hN' hlt h1 h2
              have hF := hGpos k xk
              have hF' := hGpos k xk'
              have e1 : 1 - G k xk / (N + G k xk) = N / (N + G k xk) := by field_simp; ring
              have e2 : 1 - G k xk' / (N' + G k xk') = N' / (N' + G k xk') := by field_simp; ring
              rw [e1] at h1; rw [e2] at h2
              have hr : 0 < N / (N + G k xk) := by positivity
              have hr' : 0 < N' / (N' + G k xk') := by positivity
              have hγg : 0 < P.γ * gk := mul_pos hγ hg
              have hxc : 0 < xk - P.c := by
                by_contra hh; push Not at hh
                have : P.γ * gk * (xk - P.c) * (N / (N + G k xk)) ≤ 0 :=
                  mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hγg.le hh) hr.le
                linarith
              have heq : (xk - P.c) * (N / (N + G k xk)) = (xk' - P.c) * (N' / (N' + G k xk')) := by
                have : P.γ * gk * ((xk - P.c) * (N / (N + G k xk)) - (xk' - P.c) * (N' / (N' + G k xk'))) = 0 := by
                  linarith
                rcases mul_eq_zero.mp this with h | h
                · linarith
                · linarith
              have hlt2 : N' / (N' + G k xk') < N / (N + G k xk) := by nlinarith
              rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hlt2
              nlinarith
            have hcore : ∀ (g x x' pp qq : Fin 2 → ℝ), (∀ j, 0 < g j) →
                (∀ j, 1 - P.γ * g j * (x j - P.c) *
                  (1 - G j (x j) / ((U + G (1 - j) (pp (1 - j))) + G j (x j))) = 0) →
                (∀ j, 1 - P.γ * g j * (x' j - P.c) *
                  (1 - G j (x' j) / ((U + G (1 - j) (qq (1 - j))) + G j (x' j))) = 0) →
                (∀ j, x' j ≤ x j → qq j ≤ pp j) →
                (∀ j, x j < x' j → o (x j) + o (qq j) ≤ o (x' j) + o (pp j)) →
                ∀ j, ¬ x j < x' j := by
              intro g x x' pp qq hg hf hf' hmon hk j hj
              have A := hstepA (g j) (x j) (x' j) _ _ j (hg j) (add_pos hUpos (hGpos _ _))
                (add_pos hUpos (hGpos _ _)) hj (hf j) (hf' j)
              have hF0 := hGanti j _ _ hj
              have hH1 : G (1 - j) (qq (1 - j)) < G (1 - j) (pp (1 - j)) := by
                have h1 := hGpos j (x j); have := hGpos j (x' j)
                by_contra hh; push Not at hh
                have := mul_le_mul_of_nonneg_right (add_le_add_left hh U) h1.le
                have := mul_lt_mul_of_pos_left hF0 (add_pos hUpos (hGpos (1 - j) (pp (1 - j))))
                linarith
              have hj1 : x (1 - j) < x' (1 - j) := by
                by_contra hh; push Not at hh
                have := hGanti' (1 - j) _ _ (hmon _ hh); linarith
              have B := hstepA (g (1 - j)) (x (1 - j)) (x' (1 - j)) _ _ (1 - j) (hg _)
                (add_pos hUpos (hGpos _ _)) (add_pos hUpos (hGpos _ _)) hj1 (hf (1 - j)) (hf' (1 - j))
              rw [h11] at B
              have hF1 := hGanti (1 - j) _ _ hj1
              have K0 := hGkey j _ _ _ _ (hk j hj)
              have K1 := hGkey (1 - j) _ _ _ _ (hk (1 - j) hj1)
              have := hGpos j (x j); have := hGpos j (x' j); have := hGpos j (pp j); have := hGpos j (qq j)
              have := hGpos (1 - j) (x (1 - j)); have := hGpos (1 - j) (x' (1 - j))
              have := hGpos (1 - j) (pp (1 - j)); have := hGpos (1 - j) (qq (1 - j))
              have D1 : G (1 - j) (qq (1 - j)) * G j (x j) < G (1 - j) (pp (1 - j)) * G j (x' j) := by
                nlinarith
              have D0 : G j (qq j) * G (1 - j) (x (1 - j)) < G j (pp j) * G (1 - j) (x' (1 - j)) := by
                nlinarith
              have M := mul_lt_mul'' D1 D0 (by positivity) (by positivity)
              have M2 := mul_le_mul K0 K1 (by positivity) (by positivity)
              nlinarith
            have hokey : ∀ z z', z ≤ z' → o z + o (min z' P.ps) ≤ o z' + o (min z P.ps) := by
              intro z z' h; subst ho; simp only
              have e2 : ∀ w, min (min w P.ps) P.ps = min w P.ps := fun w => by rw [min_assoc, min_self]
              rw [e2, e2]
              have e : ∀ w, max 0 (min w P.ps - P.ps) = 0 := fun w => max_eq_left (by
                have := min_le_right w P.ps; linarith)
              rw [e, e]
              have : max 0 (z - P.ps) ≤ max 0 (z' - P.ps) := max_le_max le_rfl (by linarith)
              linarith
            have hprof' : ∀ (j : Fin 2) (x y : ℝ), profitRV P lam (vs j x y) j =
                P.m * ((x - P.c) * G j x / ((U + G (1 - j) y) + G j x)) := by
              intro j x y; rw [hprofit, hsh]; ring
            have hgt : ∀ (j : Fin 2) (br : ℝ → ℝ), (∀ y, IsBestRespRV P lam j y (br y)) → ∀ y, P.c < br y := by
              intro j br hbr y
              have h := hbr y (P.c + 1)
              rw [hprof', hprof'] at h
              by_contra hh; push Not at hh
              have hd1 : 0 < U + G (1 - j) y + G j (br y) := add_pos (add_pos hUpos (hGpos _ _)) (hGpos _ _)
              have hd2 : 0 < U + G (1 - j) y + G j (P.c + 1) := add_pos (add_pos hUpos (hGpos _ _)) (hGpos _ _)
              have e1 : (br y - P.c) * G j (br y) / (U + G (1 - j) y + G j (br y)) ≤ 0 :=
                div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hGpos _ _).le) hd1.le
              have e2 : 0 < (P.c + 1 - P.c) * G j (P.c + 1) / (U + G (1 - j) y + G j (P.c + 1)) := by
                have := hGpos j (P.c + 1)
                apply div_pos _ hd2; nlinarith
              nlinarith
            have hmono : ∀ (j : Fin 2) (br : ℝ → ℝ), (∀ y, IsBestRespRV P lam j y (br y)) → Monotone br := by
              intro j br hbr y y' hyy'
              by_contra hlt; push Not at hlt
              rcases eq_or_lt_of_le hyy' with he | hy
              · rw [he] at hlt; exact lt_irrefl _ hlt
              have h1 := hbr y' (br y)
              have h2 := hbr y (br y')
              rw [hprof', hprof'] at h1 h2
              have h1' := le_of_mul_le_mul_left h1 hm
              have h2' := le_of_mul_le_mul_left h2 hm
              have hN1 := hGanti (1 - j) _ _ hy
              have hF := hGanti j _ _ hlt
              have hc1 := hgt j br hbr y
              have hc2 := hgt j br hbr y'
              have := hGpos j (br y); have := hGpos j (br y'); have := hGpos (1 - j) y; have := hGpos (1 - j) y'
              rw [div_le_div_iff₀ (by positivity) (by positivity)] at h1' h2'
              set u := (br y - P.c) * G j (br y)
              set v := (br y' - P.c) * G j (br y')
              have hu : 0 < u := by positivity
              have hv : 0 < v := by positivity
              have huv : v ≤ u := by
                by_contra hh; push Not at hh
                have := mul_lt_mul_of_pos_left hN1 (sub_pos.mpr hh)
                linarith
              have k1 := mul_lt_mul_of_pos_left hF hv
              have k2 := mul_le_mul_of_nonneg_right huv
                (add_pos (add_pos hUpos (hGpos (1 - j) y')) (hGpos j (br y'))).le
              linarith
            obtain ⟨Emax, hEmax⟩ : ∃ E : ℝ, E = G 0 P.c + G 1 P.c := ⟨_, rfl⟩
            obtain ⟨B, hB⟩ : ∃ B : ℝ, B = max P.ps (P.c + (U + Emax) / (P.γ * U)) := ⟨_, rfl⟩
            have hbound : ∀ (j : Fin 2) (br : ℝ → ℝ), (∀ y, IsBestRespRV P lam j y (br y)) → ∀ y, br y ≤ B := by
              intro j br hbr y
              rcases le_or_gt (br y) P.ps with h | h
              · rw [hB]; exact h.trans (le_max_left _ _)
              have hf := (hBR j y (br y) (hbr y)).1 h
              rw [hsh] at hf
              have hc1 := hgt j br hbr y
              have hFle : G j (br y) ≤ Emax := by
                have := hGanti' j _ _ hc1.le
                have := hGpos 0 P.c; have := hGpos 1 P.c
                have hGj : G j P.c ≤ Emax := by
                  fin_cases j
                  · rw [hEmax]; show G 0 P.c ≤ G 0 P.c + G 1 P.c; linarith only [hGpos 1 P.c]
                  · rw [hEmax]; show G 1 P.c ≤ G 0 P.c + G 1 P.c; linarith only [hGpos 0 P.c]
                exact le_trans (hGanti' j _ _ hc1.le) hGj
              have hNpos := hGpos (1 - j) y
              have hF := hGpos j (br y)
              have hd : 0 < U + G (1 - j) y + G j (br y) := by linarith only [hNpos, hF, hUpos]
              have e1 : 1 - G j (br y) / (U + G (1 - j) y + G j (br y)) =
                  (U + G (1 - j) y) / (U + G (1 - j) y + G j (br y)) := by field_simp; ring
              rw [e1] at hf
              have hf1 : P.γ * (br y - P.c) * ((U + G (1 - j) y) / (U + G (1 - j) y + G j (br y))) = 1 := by
                linarith only [hf]
              rw [mul_div_assoc', div_eq_one_iff_eq hd.ne'] at hf1
              have k1 : (br y - P.c) * (P.γ * U) * (U + G (1 - j) y) =
                  U * (U + G (1 - j) y) + U * G j (br y) := by
                have : (br y - P.c) * (P.γ * U) * (U + G (1 - j) y) =
                    U * (P.γ * (br y - P.c) * (U + G (1 - j) y)) := by ring
                rw [this, hf1]; ring
              have k2 : U * G j (br y) ≤ Emax * (U + G (1 - j) y) := by
                rw [mul_comm U]
                exact mul_le_mul hFle (by linarith only [hNpos]) hUpos.le (by linarith only [hFle, hF])
              have : br y - P.c ≤ (U + Emax) / (P.γ * U) := by
                rw [le_div_iff₀ (mul_pos hγ hUpos)]
                have h3 : (br y - P.c) * (P.γ * U) * (U + G (1 - j) y) ≤ (U + Emax) * (U + G (1 - j) y) := by
                  rw [k1]
                  have : (U + Emax) * (U + G (1 - j) y) = U * (U + G (1 - j) y) + Emax * (U + G (1 - j) y) := by
                    ring
                  rw [this]; linarith only [k2]
                exact le_of_mul_le_mul_right h3 (by linarith only [hNpos, hUpos])
              have h4 : br y ≤ P.c + (U + Emax) / (P.γ * U) := by linarith only [this]
              rw [hB]; exact le_trans h4 (le_max_right _ _)
            obtain ⟨br0, hbr0⟩ := (hA5 0).1
            obtain ⟨br1, hbr1⟩ := (hA5 1).1
            have hfm : Monotone (fun y => br1 (br0 y)) := (hmono 1 br1 hbr1).comp (hmono 0 br0 hbr0)
            have hbdd : BddAbove {y | y ≤ br1 (br0 y)} := ⟨B, fun y hy => hy.trans (hbound 1 br1 hbr1 _)⟩
            have hne : P.c ∈ {y | y ≤ br1 (br0 y)} := (hgt 1 br1 hbr1 _).le
            obtain ⟨ys, hys⟩ : ∃ ys : ℝ, ys = sSup {y | y ≤ br1 (br0 y)} := ⟨_, rfl⟩
            have hfix1 : ys ≤ br1 (br0 ys) := by
              have h0 : sSup {y | y ≤ br1 (br0 y)} ≤ br1 (br0 (sSup {y | y ≤ br1 (br0 y)})) :=
                csSup_le ⟨_, hne⟩ (fun y hy => le_trans hy (hfm (le_csSup hbdd hy)))
              rw [← hys] at h0; exact h0
            have hmem : br1 (br0 ys) ∈ {y | y ≤ br1 (br0 y)} := hfm hfix1
            have hfix2 : br1 (br0 ys) ≤ ys := by
              have h0 := le_csSup hbdd hmem
              rw [← hys] at h0; exact h0
            have hfix : br1 (br0 ys) = ys := le_antisymm hfix2 hfix1
            refine ⟨⟨vs 0 (br0 ys) ys, fun _ => Set.mem_univ _, ?_⟩, ?_⟩
            · refine Fin.forall_fin_two.mpr ⟨fun x _ => ?_, fun x _ => ?_⟩
              · show profitRV P lam (Function.update (vs 0 (br0 ys) ys) 0 x) 0 ≤
                  profitRV P lam (vs 0 (br0 ys) ys) 0
                rw [hvs0]; exact hbr0 ys x
              · show profitRV P lam (Function.update (vs 0 (br0 ys) ys) 1 x) 1 ≤
                  profitRV P lam (vs 0 (br0 ys) ys) 1
                rw [hvs1, hvs01]
                have := hbr1 (br0 ys) x
                rwa [hfix] at this
            intro p hp
            obtain ⟨hp1, hp2⟩ := hpart2 p hp
            refine ⟨hp1, hp2, ?_⟩
            intro q hq1 hq2
            have hdat : ∀ j : Fin 2, ∃ gj xj xj' : ℝ, 0 < gj ∧
                1 - P.γ * gj * (xj - P.c) * (1 - G j xj / ((U + G (1 - j) (p (1 - j))) + G j xj)) = 0 ∧
                1 - P.γ * gj * (xj' - P.c) * (1 - G j xj' / ((U + G (1 - j) (q (1 - j))) + G j xj')) = 0 ∧
                (xj' ≤ xj → q j ≤ p j) ∧ (xj ≤ xj' → p j ≤ q j) ∧
                (xj < xj' → o xj + o (q j) ≤ o xj' + o (p j)) ∧
                (xj' < xj → o xj' + o (p j) ≤ o xj + o (q j)) ∧ (xj = xj' → p j = q j) := by
              intro j
              rcases lt_or_ge P.ps (p j) with h | h
              · obtain ⟨hq0, hqf⟩ := hq1 j h
                have hpf := hp1 j h
                rw [hsp] at hpf hqf
                refine ⟨1, p j, q j, one_pos, by rw [mul_one]; exact hpf, by rw [mul_one]; exact hqf,
                  fun h => h, fun h => h, fun _ => by linarith, fun _ => by linarith, fun h => h⟩
              · obtain ⟨ph, hpf, hpe⟩ := hp2 j h
                obtain ⟨qh, hqf, hqe⟩ := hq2 j h
                rw [hsh] at hpf hqf
                refine ⟨lam, ph, qh, hl0, hpf, hqf, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
                  fun h => ?_⟩
                · rw [hpe, hqe]; exact min_le_min_right _ h
                · rw [hpe, hqe]; exact min_le_min_right _ h
                · rw [hpe, hqe]; exact hokey _ _ h.le
                · rw [hpe, hqe]; exact hokey _ _ h.le
                · rw [hpe, hqe, h]
            choose g x x' hg hfp hfq hm1 hm2 hk1 hk2 heq using hdat
            have c1 := hcore g x x' p q hg hfp hfq hm1 hk1
            have c2 := hcore g x' x q p hg hfq hfp hm2 hk2
            funext j
            have : x j = x' j := by
              rcases lt_trichotomy (x j) (x' j) with h | h | h
              · exact absurd h (c1 j)
              · exact h
              · exact absurd h (c2 j)
            exact (heq j this).symm
