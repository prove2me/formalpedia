-- Prove2me | solution 1 for HealthRefPricing.PriceCompare.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T01:08:57.344485+00:00
-- url     : https://prove2.me/submissions/cd52d59f-a40e-46af-aee1-77e661845839

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

set_option autoImplicit false

namespace HRP5Aux

open Real

/-- Normalised first-order-condition residual in markup coordinates `t = α (p - c)`. -/
noncomputable def K (A0 A1 B x y : ℝ) : ℝ := x - 1 - exp (A0 - x) / (exp B + exp (A1 - y))

lemma frac_pos (A0 A1 B x y : ℝ) : 0 < exp (A0 - x) / (exp B + exp (A1 - y)) := by positivity

lemma one_lt_of_K_eq (A0 A1 B x y : ℝ) (h : K A0 A1 B x y = 0) : 1 < x := by
  unfold K at h; have := frac_pos A0 A1 B x y; linarith

lemma cmp_half (A0 A1 B B' u0 u1 v0 v1 : ℝ) (hB : B ≤ B')
    (hu : 0 ≤ K A0 A1 B u0 u1) (hv : K A0 A1 B' v0 v1 ≤ 0) (h1 : v1 - u1 ≤ v0 - u0) :
    v0 ≤ u0 := by
  by_contra h
  push_neg at h
  have hfr : exp (A0 - v0) / (exp B' + exp (A1 - v1)) ≤
      exp (A0 - u0) / (exp B + exp (A1 - u1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : exp (A0 - v0) * (exp B + exp (A1 - u1)) =
        exp (A0 - v0 + B) + exp (A0 - v0 + (A1 - u1)) := by
      rw [mul_add, ← exp_add, ← exp_add]
    have e2 : exp (A0 - u0) * (exp B' + exp (A1 - v1)) =
        exp (A0 - u0 + B') + exp (A0 - u0 + (A1 - v1)) := by
      rw [mul_add, ← exp_add, ← exp_add]
    rw [e1, e2]
    have i1 : exp (A0 - v0 + B) ≤ exp (A0 - u0 + B') := exp_le_exp.mpr (by linarith)
    have i2 : exp (A0 - v0 + (A1 - u1)) ≤ exp (A0 - u0 + (A1 - v1)) :=
      exp_le_exp.mpr (by linarith)
    linarith
  unfold K at hu hv
  linarith

lemma cmp2 (A0 A1 B B' u0 u1 v0 v1 : ℝ) (hB : B ≤ B')
    (hu0 : 0 ≤ K A0 A1 B u0 u1) (hu1 : 0 ≤ K A1 A0 B u1 u0)
    (hv0 : K A0 A1 B' v0 v1 ≤ 0) (hv1 : K A1 A0 B' v1 v0 ≤ 0) : v0 ≤ u0 ∧ v1 ≤ u1 := by
  rcases le_total (v1 - u1) (v0 - u0) with h | h
  · have := cmp_half A0 A1 B B' u0 u1 v0 v1 hB hu0 hv0 h
    exact ⟨this, by linarith⟩
  · have := cmp_half A1 A0 B B' u1 u0 v1 v0 hB hu1 hv1 h
    exact ⟨by linarith, this⟩

lemma K_shift (A0 A1 B x y η : ℝ) : K A0 A1 B (x - η) (y - η) = K A0 A1 (B - η) x y - η := by
  unfold K
  have hn : exp (A0 - (x - η)) = exp (A0 - x) * exp η := by rw [← exp_add]; congr 1; ring
  have hd : exp B + exp (A1 - (y - η)) = (exp (B - η) + exp (A1 - y)) * exp η := by
    rw [add_mul, ← exp_add, ← exp_add]; congr 1 <;> (congr 1; ring)
  rw [hn, hd, mul_div_mul_right _ _ (exp_pos η).ne']
  ring

lemma scale (A A' u0 α c s x y : ℝ) :
    exp (A - α * x) / (exp u0 + exp (A' - α * y)) =
      exp ((A - s) - α * (x - c)) / (exp (u0 + α * c - s) + exp ((A' - s) - α * (y - c))) := by
  have hn : exp (A - α * x) = exp ((A - s) - α * (x - c)) * exp (s - α * c) := by
    rw [← exp_add]; congr 1; ring
  have hd : exp u0 + exp (A' - α * y) =
      (exp (u0 + α * c - s) + exp ((A' - s) - α * (y - c))) * exp (s - α * c) := by
    rw [add_mul, ← exp_add, ← exp_add]; congr 1 <;> (congr 1; ring)
  rw [hn, hd, mul_div_mul_right _ _ (exp_pos _).ne']

lemma hasDeriv_F (M c R α A x0 : ℝ) (hR : 0 < R) :
    HasDerivAt (fun x => M * (x - c) * (exp (A - α * x) / (R + exp (A - α * x))))
      (M * (exp (A - α * x0) / (R + exp (A - α * x0))) *
        (1 - α * (x0 - c) * R / (R + exp (A - α * x0)))) x0 := by
  have h1 : HasDerivAt (fun x => A - α * x) (-α) x0 := by
    simpa using ((hasDerivAt_id x0).const_mul α).const_sub A
  have hw : HasDerivAt (fun x => exp (A - α * x)) (exp (A - α * x0) * (-α)) x0 := h1.exp
  have hden : HasDerivAt (fun x => R + exp (A - α * x)) (exp (A - α * x0) * (-α)) x0 :=
    hw.const_add R
  have hpos : R + exp (A - α * x0) ≠ 0 := by positivity
  have hq := hw.div hden hpos
  have hl : HasDerivAt (fun x => M * (x - c)) M x0 := by
    simpa using ((hasDerivAt_id x0).sub_const c).const_mul M
  have := hl.mul hq
  refine this.congr_deriv ?_
  simp only [Pi.div_apply]
  field_simp
  ring

lemma foc_eq (M c R α A x0 : ℝ) (hM : 0 < M) (hR : 0 < R)
    (hmax : ∀ x, M * (x - c) * (exp (A - α * x) / (R + exp (A - α * x))) ≤
      M * (x0 - c) * (exp (A - α * x0) / (R + exp (A - α * x0)))) :
    α * (x0 - c) = 1 + exp (A - α * x0) / R := by
  have hd := hasDeriv_F M c R α A x0 hR
  have hlm : IsLocalMax (fun x => M * (x - c) * (exp (A - α * x) / (R + exp (A - α * x)))) x0 :=
    Filter.Eventually.of_forall hmax
  have h0 := hlm.hasDerivAt_eq_zero hd
  have hp : 0 < M * (exp (A - α * x0) / (R + exp (A - α * x0))) := by positivity
  have h2 : 1 - α * (x0 - c) * R / (R + exp (A - α * x0)) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exact h
  have hw : 0 < R + exp (A - α * x0) := by positivity
  rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hw.ne'] at h2
  have : exp (A - α * x0) / R = α * (x0 - c) - 1 := by
    rw [div_eq_iff hR.ne']; linarith
  linarith

lemma foc_ge (M c R α A x0 : ℝ) (hM : 0 < M) (hR : 0 < R)
    (hmax : ∀ x, x0 < x → M * (x - c) * (exp (A - α * x) / (R + exp (A - α * x))) ≤
      M * (x0 - c) * (exp (A - α * x0) / (R + exp (A - α * x0)))) :
    1 + exp (A - α * x0) / R ≤ α * (x0 - c) := by
  have hd := hasDeriv_F M c R α A x0 hR
  have ht := hd.tendsto_slope_zero_right
  have hD : M * (exp (A - α * x0) / (R + exp (A - α * x0))) *
      (1 - α * (x0 - c) * R / (R + exp (A - α * x0))) ≤ 0 := by
    refine le_of_tendsto ht ?_
    refine eventually_nhdsWithin_of_forall (fun t (htp : 0 < t) => ?_)
    have := hmax (x0 + t) (by linarith)
    rw [smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr htp.le) (by linarith)
  have hp : 0 < M * (exp (A - α * x0) / (R + exp (A - α * x0))) := by positivity
  have h2 : 1 ≤ α * (x0 - c) * R / (R + exp (A - α * x0)) := by
    by_contra hc
    push_neg at hc
    have := mul_pos hp (by linarith : 0 < 1 - α * (x0 - c) * R / (R + exp (A - α * x0)))
    linarith
  have hw : 0 < R + exp (A - α * x0) := by positivity
  rw [le_div_iff₀ hw, one_mul] at h2
  have : exp (A - α * x0) / R ≤ α * (x0 - c) - 1 := by
    rw [div_le_iff₀ hR]; linarith
  linarith

open HealthRefPricing.PriceCompare

lemma sum_two (f : Fin 2 → ℝ) (k : Fin 2) : ∑ i, f i = f k + f (k + 1) := by
  fin_cases k <;> simp [Fin.sum_univ_two] <;> ring

lemma succ_ne (k : Fin 2) : k + 1 ≠ k := by fin_cases k <;> decide

lemma upd_ne (p : Fin 2 → ℝ) (k : Fin 2) (x : ℝ) :
    Function.update p k x (k + 1) = p (k + 1) := Function.update_of_ne (succ_ne k) _ _

lemma vp_form (P : Params) (lam : ℝ) (p : Fin 2 → ℝ) (k : Fin 2) (x : ℝ) :
    profitVP P lam (Function.update p k x) k =
      P.m * (x - P.c) * (exp (P.a k - P.γ * lam * x) /
        ((exp P.u0 + exp (P.a (k + 1) - P.γ * lam * p (k + 1))) +
          exp (P.a k - P.γ * lam * x))) := by
  unfold profitVP share oopVP
  rw [sum_two _ k]
  simp only [Function.update_self, upd_ne]
  ring_nf

lemma rp_form (P : Params) (pRP : Fin 2 → ℝ) (k : Fin 2) (x : ℝ) (hx : P.ps ≤ x)
    (hl : P.ps ≤ pRP (k + 1)) :
    profitRP P (Function.update pRP k x) k =
      P.m * (x - P.c) * (exp ((P.a k + P.γ * (P.ps - P.ct)) - P.γ * x) /
        ((exp P.u0 + exp ((P.a (k + 1) + P.γ * (P.ps - P.ct)) - P.γ * pRP (k + 1))) +
          exp ((P.a k + P.γ * (P.ps - P.ct)) - P.γ * x))) := by
  unfold profitRP share oopRP
  rw [sum_two _ k]
  simp only [Function.update_self, upd_ne]
  rw [max_eq_right (by linarith : (0:ℝ) ≤ x - P.ps),
    max_eq_right (by linarith : (0:ℝ) ≤ pRP (k + 1) - P.ps)]
  ring_nf

lemma vp_K (P : Params) (hm : 0 < P.m) (lam : ℝ) (p : Fin 2 → ℝ) (hp : IsEqVP P lam p)
    (k : Fin 2) :
    K (P.a k) (P.a (k + 1)) (P.u0 + P.γ * lam * P.c) (P.γ * lam * (p k - P.c))
      (P.γ * lam * (p (k + 1) - P.c)) = 0 := by
  have hRpos : 0 < exp P.u0 + exp (P.a (k + 1) - P.γ * lam * p (k + 1)) := by positivity
  have hmax : ∀ x, P.m * (x - P.c) * (exp (P.a k - P.γ * lam * x) /
        ((exp P.u0 + exp (P.a (k + 1) - P.γ * lam * p (k + 1))) +
          exp (P.a k - P.γ * lam * x))) ≤
      P.m * (p k - P.c) * (exp (P.a k - P.γ * lam * p k) /
        ((exp P.u0 + exp (P.a (k + 1) - P.γ * lam * p (k + 1))) +
          exp (P.a k - P.γ * lam * p k))) := by
    intro x
    have h := hp.2 k x (Set.mem_univ _)
    have e1 := vp_form P lam p k x
    have e2 := vp_form P lam p k (p k)
    rw [Function.update_eq_self] at e2
    rw [← e1, ← e2]
    exact h
  have hfoc := foc_eq P.m P.c _ (P.γ * lam) (P.a k) (p k) hm hRpos hmax
  rw [scale (P.a k) (P.a (k + 1)) P.u0 (P.γ * lam) P.c 0 (p k) (p (k + 1))] at hfoc
  simp only [sub_zero] at hfoc
  unfold K
  linarith

lemma rp_ge (P : Params) (hm : 0 < P.m) (pRP : Fin 2 → ℝ) (hRP : IsEqRP P pRP) (k : Fin 2) :
    P.ps ≤ pRP k := by
  by_contra h
  push_neg at h
  have h1 := hRP.2 k P.ps (Set.mem_univ _)
  have hoop : oopRP P (Function.update pRP k P.ps) = oopRP P pRP := by
    funext i
    unfold oopRP
    by_cases hi : i = k
    · subst hi
      rw [Function.update_self, sub_self, max_eq_left (by linarith : pRP i - P.ps ≤ 0), max_self]
    · rw [Function.update_of_ne hi]
  simp only [profitRP] at h1
  rw [hoop, Function.update_self] at h1
  have hs : 0 < share P (oopRP P pRP) k := by unfold share; positivity
  have := mul_pos hm hs
  nlinarith

lemma rp_K (P : Params) (hm : 0 < P.m) (pRP : Fin 2 → ℝ) (hRP : IsEqRP P pRP) (k : Fin 2) :
    0 ≤ K (P.a k) (P.a (k + 1)) (P.u0 + P.γ * P.c - P.γ * (P.ps - P.ct))
      (P.γ * (pRP k - P.c)) (P.γ * (pRP (k + 1) - P.c)) := by
  have hk := rp_ge P hm pRP hRP k
  have hl := rp_ge P hm pRP hRP (k + 1)
  have hRpos : 0 < exp P.u0 +
      exp ((P.a (k + 1) + P.γ * (P.ps - P.ct)) - P.γ * pRP (k + 1)) := by positivity
  have hmax : ∀ x, pRP k < x →
      P.m * (x - P.c) * (exp ((P.a k + P.γ * (P.ps - P.ct)) - P.γ * x) /
        ((exp P.u0 + exp ((P.a (k + 1) + P.γ * (P.ps - P.ct)) - P.γ * pRP (k + 1))) +
          exp ((P.a k + P.γ * (P.ps - P.ct)) - P.γ * x))) ≤
      P.m * (pRP k - P.c) * (exp ((P.a k + P.γ * (P.ps - P.ct)) - P.γ * pRP k) /
        ((exp P.u0 + exp ((P.a (k + 1) + P.γ * (P.ps - P.ct)) - P.γ * pRP (k + 1))) +
          exp ((P.a k + P.γ * (P.ps - P.ct)) - P.γ * pRP k))) := by
    intro x hx
    have h := hRP.2 k x (Set.mem_univ _)
    have e1 := rp_form P pRP k x (by linarith) hl
    have e2 := rp_form P pRP k (pRP k) hk hl
    rw [Function.update_eq_self] at e2
    rw [← e1, ← e2]
    exact h
  have hfoc := foc_ge P.m P.c _ P.γ (P.a k + P.γ * (P.ps - P.ct)) (pRP k) hm hRpos hmax
  rw [scale (P.a k + P.γ * (P.ps - P.ct)) (P.a (k + 1) + P.γ * (P.ps - P.ct)) P.u0 P.γ P.c
    (P.γ * (P.ps - P.ct)) (pRP k) (pRP (k + 1))] at hfoc
  simp only [add_sub_cancel_right] at hfoc
  unfold K
  linarith

lemma vp_K01 (P : Params) (hm : 0 < P.m) (lam : ℝ) (p : Fin 2 → ℝ) (hp : IsEqVP P lam p) :
    K (P.a 0) (P.a 1) (P.u0 + P.γ * lam * P.c) (P.γ * lam * (p 0 - P.c))
      (P.γ * lam * (p 1 - P.c)) = 0 ∧
    K (P.a 1) (P.a 0) (P.u0 + P.γ * lam * P.c) (P.γ * lam * (p 1 - P.c))
      (P.γ * lam * (p 0 - P.c)) = 0 :=
  ⟨vp_K P hm lam p hp 0, vp_K P hm lam p hp 1⟩

lemma rp_K01 (P : Params) (hm : 0 < P.m) (pRP : Fin 2 → ℝ) (hRP : IsEqRP P pRP) :
    0 ≤ K (P.a 0) (P.a 1) (P.u0 + P.γ * P.c - P.γ * (P.ps - P.ct))
      (P.γ * (pRP 0 - P.c)) (P.γ * (pRP 1 - P.c)) ∧
    0 ≤ K (P.a 1) (P.a 0) (P.u0 + P.γ * P.c - P.γ * (P.ps - P.ct))
      (P.γ * (pRP 1 - P.c)) (P.γ * (pRP 0 - P.c)) :=
  ⟨rp_K P hm pRP hRP 0, rp_K P hm pRP hRP 1⟩

lemma fin2_cases (j : Fin 2) (Q : Fin 2 → Prop) (h0 : Q 0) (h1 : Q 1) : Q j := by
  fin_cases j
  · exact h0
  · exact h1

lemma finish_mono (g l l' x x' c : ℝ) (hg : 0 < g) (hl : 0 < l) (hll : l ≤ l')
    (ht : 1 < g * l * (x - c)) (h : g * l' * (x' - c) ≤ g * l * (x - c)) : x' ≤ x := by
  by_contra hx
  push_neg at hx
  have hgl : 0 < g * l := mul_pos hg hl
  have hxc : 0 < x - c := by
    by_contra hneg; push_neg at hneg
    have : g * l * (x - c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hgl.le hneg
    linarith
  have hgl' : 0 < g * l' := mul_pos hg (lt_of_lt_of_le hl hll)
  have i1 : g * l' * (x - c) < g * l' * (x' - c) := mul_lt_mul_of_pos_left (by linarith) hgl'
  have i2 : g * l * (x - c) ≤ g * l' * (x - c) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hll hg.le) hxc.le
  linarith

lemma vp_mono (P : Params) (hm : 0 < P.m) (hγ : 0 < P.γ) (hc : 0 ≤ P.c) (lam lam' : ℝ)
    (hl : 0 < lam) (hll : lam ≤ lam') (p p' : Fin 2 → ℝ) (hp : IsEqVP P lam p)
    (hp' : IsEqVP P lam' p') (j : Fin 2) : p' j ≤ p j := by
  have hB : P.u0 + P.γ * lam * P.c ≤ P.u0 + P.γ * lam' * P.c := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hll hγ.le) hc
    linarith
  obtain ⟨a0, a1⟩ := vp_K01 P hm lam p hp
  obtain ⟨b0, b1⟩ := vp_K01 P hm lam' p' hp'
  obtain ⟨c0, c1⟩ := cmp2 _ _ _ _ _ _ _ _ hB a0.ge a1.ge b0.le b1.le
  refine fin2_cases j (fun i => p' i ≤ p i) ?_ ?_
  · exact finish_mono _ _ _ _ _ _ hγ hl hll (one_lt_of_K_eq _ _ _ _ _ a0) c0
  · exact finish_mono _ _ _ _ _ _ hγ hl hll (one_lt_of_K_eq _ _ _ _ _ a1) c1

lemma vp_lower (P : Params) (hm : 0 < P.m) (hγ : 0 < P.γ) (hc : 0 ≤ P.c) (lam lam' : ℝ)
    (hll : lam ≤ lam') (p p' : Fin 2 → ℝ) (hp : IsEqVP P lam p)
    (hp' : IsEqVP P lam' p') (j : Fin 2) :
    P.γ * lam * (p j - P.c) - P.γ * P.c * (lam' - lam) ≤ P.γ * lam' * (p' j - P.c) := by
  have hη : 0 ≤ P.γ * P.c * (lam' - lam) :=
    mul_nonneg (mul_nonneg hγ.le hc) (by linarith)
  obtain ⟨a0, a1⟩ := vp_K01 P hm lam p hp
  obtain ⟨b0, b1⟩ := vp_K01 P hm lam' p' hp'
  have hBe : P.u0 + P.γ * lam' * P.c - P.γ * P.c * (lam' - lam) = P.u0 + P.γ * lam * P.c := by
    ring
  have s0 := K_shift (P.a 0) (P.a 1) (P.u0 + P.γ * lam' * P.c) (P.γ * lam * (p 0 - P.c))
    (P.γ * lam * (p 1 - P.c)) (P.γ * P.c * (lam' - lam))
  have s1 := K_shift (P.a 1) (P.a 0) (P.u0 + P.γ * lam' * P.c) (P.γ * lam * (p 1 - P.c))
    (P.γ * lam * (p 0 - P.c)) (P.γ * P.c * (lam' - lam))
  rw [hBe, a0] at s0
  rw [hBe, a1] at s1
  obtain ⟨c0, c1⟩ := cmp2 _ _ _ _ _ _ _ _ le_rfl b0.ge b1.ge (by rw [s0]; linarith)
    (by rw [s1]; linarith)
  refine fin2_cases j (fun i => P.γ * lam * (p i - P.c) - P.γ * P.c * (lam' - lam) ≤
    P.γ * lam' * (p' i - P.c)) ?_ ?_
  · exact c0
  · exact c1

lemma rp_vs_vp (P : Params) (hm : 0 < P.m) (hγ : 0 < P.γ) (hct : P.ct < P.ps)
    (pRP : Fin 2 → ℝ) (hRP : IsEqRP P pRP) (p : Fin 2 → ℝ) (hp : IsEqVP P 1 p) (j : Fin 2) :
    p j ≤ pRP j := by
  obtain ⟨a0, a1⟩ := rp_K01 P hm pRP hRP
  obtain ⟨b0, b1⟩ := vp_K01 P hm 1 p hp
  have hB : P.u0 + P.γ * P.c - P.γ * (P.ps - P.ct) ≤ P.u0 + P.γ * 1 * P.c := by
    have := mul_pos hγ (sub_pos.mpr hct)
    nlinarith
  obtain ⟨c0, c1⟩ := cmp2 _ _ _ _ _ _ _ _ hB a0 a1 b0.le b1.le
  refine fin2_cases j (fun i => p i ≤ pRP i) ?_ ?_
  · rw [mul_one] at c0
    exact le_of_sub_nonneg (by nlinarith)
  · rw [mul_one] at c1
    exact le_of_sub_nonneg (by nlinarith)

end HRP5Aux

open HealthRefPricing.PriceCompare in
theorem solution (P : Params) (hS : P.Standing)
    (hA1 : ∀ lam ∈ Set.Ioc (0 : ℝ) 1, Assumption1 P lam) (hA2 : Assumption2 P)
    (hct : P.ct < P.ps) (pRP : Fin 2 → ℝ) (hRP : IsEqRP P pRP) (j : Fin 2) :
    ∃ lamStar ∈ Set.Ioc (0 : ℝ) 1, ∀ lam ∈ Set.Ioc (0 : ℝ) 1, ∀ p : Fin 2 → ℝ, IsEqVP P lam p →
      (pRP j < p j ↔ lam < lamStar) := by
  obtain ⟨hm, hγ, hc, -, -⟩ := hS
  let L : Set ℝ := {l | l ∈ Set.Ioc (0 : ℝ) 1 ∧ ∃ p : Fin 2 → ℝ, IsEqVP P l p ∧ p j ≤ pRP j}
  have hbdd : BddBelow L := ⟨0, fun l hl => hl.1.1.le⟩
  by_cases hL : L.Nonempty
  · obtain ⟨l0, hl0, p0, hp0, hq0⟩ := hL
    -- every member of `L` is bounded below by a positive constant
    have ht0 : 1 < P.γ * l0 * (p0 j - P.c) := by
      refine HRP5Aux.fin2_cases j (fun i => 1 < P.γ * l0 * (p0 i - P.c)) ?_ ?_
      · exact HRP5Aux.one_lt_of_K_eq _ _ _ _ _ (HRP5Aux.vp_K01 P hm l0 p0 hp0).1
      · exact HRP5Aux.one_lt_of_K_eq _ _ _ _ _ (HRP5Aux.vp_K01 P hm l0 p0 hp0).2
    have hqc : 0 < pRP j - P.c := by
      by_contra hneg; push_neg at hneg
      have h1 : P.γ * l0 * (p0 j - P.c) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_pos hγ hl0.1).le (by linarith)
      linarith
    have hq0pos : 0 < pRP j := by linarith
    have hlb : ∀ l ∈ L, 1 / (P.γ * (pRP j - P.c)) ≤ l := by
      intro l hl
      obtain ⟨hl1, p', hp', hle⟩ := hl
      have ht : 1 < P.γ * l * (p' j - P.c) := by
        refine HRP5Aux.fin2_cases j (fun i => 1 < P.γ * l * (p' i - P.c)) ?_ ?_
        · exact HRP5Aux.one_lt_of_K_eq _ _ _ _ _ (HRP5Aux.vp_K01 P hm l p' hp').1
        · exact HRP5Aux.one_lt_of_K_eq _ _ _ _ _ (HRP5Aux.vp_K01 P hm l p' hp').2
      have hpos : 0 < P.γ * (pRP j - P.c) := mul_pos hγ hqc
      rw [div_le_iff₀ hpos]
      have : P.γ * l * (p' j - P.c) ≤ P.γ * l * (pRP j - P.c) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_pos hγ hl1.1).le
      nlinarith
    have hLne : L.Nonempty := ⟨l0, hl0, p0, hp0, hq0⟩
    have hstar_pos : 0 < sInf L :=
      lt_of_lt_of_le (by have := mul_pos hγ hqc; positivity) (le_csInf hLne hlb)
    have hstar_le : sInf L ≤ 1 := le_trans (csInf_le hbdd ⟨hl0, p0, hp0, hq0⟩) hl0.2
    refine ⟨sInf L, ⟨hstar_pos, hstar_le⟩, ?_⟩
    intro lam hlam p hp
    constructor
    · intro hgt
      by_contra hge
      push_neg at hge
      have hμ : lam < lam * p j / pRP j := by
        rw [lt_div_iff₀ hq0pos]
        exact mul_lt_mul_of_pos_left hgt hlam.1
      obtain ⟨l, hlL, hlμ⟩ := exists_lt_of_csInf_lt hLne (lt_of_le_of_lt hge hμ)
      obtain ⟨hl, p'', hp'', hle⟩ := hlL
      rcases le_or_gt l lam with h | h
      · have := HRP5Aux.vp_mono P hm hγ hc l lam hl.1 h p'' p hp'' hp j
        linarith
      · have hlow := HRP5Aux.vp_lower P hm hγ hc lam l h.le p p'' hp hp'' j
        have hlq : l * pRP j < lam * p j := by rwa [lt_div_iff₀ hq0pos] at hlμ
        have i1 : P.γ * l * p'' j ≤ P.γ * l * pRP j :=
          mul_le_mul_of_nonneg_left hle (mul_pos hγ hl.1).le
        have i2 := mul_pos hγ (sub_pos.mpr hlq)
        nlinarith
    · intro hlt
      by_contra hle
      push_neg at hle
      have : sInf L ≤ lam := csInf_le hbdd ⟨hlam, p, hp, hle⟩
      linarith
  · refine ⟨1, ⟨one_pos, le_rfl⟩, ?_⟩
    intro lam hlam p hp
    constructor
    · intro hgt
      rcases lt_or_eq_of_le hlam.2 with h | h
      · exact h
      · subst h
        have := HRP5Aux.rp_vs_vp P hm hγ hct pRP hRP p hp j
        linarith
    · intro _
      by_contra hle
      push_neg at hle
      exact hL ⟨lam, hlam, p, hp, hle⟩
