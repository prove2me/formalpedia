-- Prove2me | solution 1 for ModernConvex.SLemma.polyak_convexity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T01:35:23.03042+00:00
-- url     : https://prove2.me/submissions/ea86c828-de65-44df-8f28-a614d5743cd0

import Mathlib

open Matrix

namespace PC101

variable {n : ℕ}

def qf (Q : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) : ℝ := u ⬝ᵥ (Q *ᵥ u)

def bf (Q : Matrix (Fin n) (Fin n) ℝ) (u w : Fin n → ℝ) : ℝ := u ⬝ᵥ (Q *ᵥ w) + w ⬝ᵥ (Q *ᵥ u)

lemma qf3 (Q : Matrix (Fin n) (Fin n) ℝ) (a c d : ℝ) (x y w : Fin n → ℝ) :
    qf Q (a • x + c • y + d • w) = a ^ 2 * qf Q x + c ^ 2 * qf Q y + d ^ 2 * qf Q w
      + a * c * bf Q x y + a * d * bf Q x w + c * d * bf Q y w := by
  simp only [qf, bf, mulVec_add, mulVec_smul, dotProduct_add,
    add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma bf_lin (Q : Matrix (Fin n) (Fin n) ℝ) (a c d : ℝ) (z x y w : Fin n → ℝ) :
    bf Q z (a • x + c • y + d • w) = a * bf Q z x + c * bf Q z y + d * bf Q z w := by
  simp only [bf, mulVec_add, mulVec_smul, dotProduct_add,
    add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma bf_self (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : bf Q x x = 2 * qf Q x := by
  simp only [bf, qf]; ring

lemma bf_comm (Q : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) : bf Q x y = bf Q y x := by
  simp only [bf]; ring

lemma qf_smul (Q : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (x : Fin n → ℝ) :
    qf Q (a • x) = a ^ 2 * qf Q x := by
  simp only [qf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

lemma bf_smul (Q : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (x y : Fin n → ℝ) :
    bf Q x (a • y) = a * bf Q x y := by
  simpa using bf_lin Q a 0 0 x y y y

lemma qf_neg (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : qf Q (-x) = qf Q x := by
  simpa using qf_smul Q (-1) x

lemma bf_neg (Q : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) : bf Q x (-y) = - bf Q x y := by
  simpa using bf_smul Q (-1) x y

lemma bf_zero (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : bf Q x 0 = 0 := by
  simp [bf]

/-- every value between `h x` and `h y` is attained by `h` on the punctured cone `qf Q = 0`. -/
def Good (Q : Matrix (Fin n) (Fin n) ℝ) (h : (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : Prop :=
  ∀ r ∈ Set.uIcc (h x) (h y), ∃ e, e ≠ 0 ∧ qf Q e = 0 ∧ h e = r

lemma good_path (Q : Matrix (Fin n) (Fin n) ℝ) (h : (Fin n → ℝ) → ℝ)
    (hh : ContinuousOn h {x | x ≠ 0}) (v : ℝ → Fin n → ℝ) (hc : Continuous v)
    (hv : ∀ θ ∈ Set.Icc (0:ℝ) 1, v θ ≠ 0) (hq : ∀ θ ∈ Set.Icc (0:ℝ) 1, qf Q (v θ) = 0) :
    Good Q h (v 0) (v 1) := by
  intro r hr
  have hcont : ContinuousOn (h ∘ v) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact hh.comp hc.continuousOn (fun θ hθ => hv θ hθ)
  obtain ⟨θ, hθ, hθr⟩ := intermediate_value_uIcc hcont hr
  rw [Set.uIcc_of_le zero_le_one] at hθ
  exact ⟨v θ, hv θ hθ, hq θ hθ, hθr⟩

lemma good_trans (Q : Matrix (Fin n) (Fin n) ℝ) (h : (Fin n → ℝ) → ℝ) (x w y : Fin n → ℝ)
    (h1 : Good Q h x w) (h2 : Good Q h w y) : Good Q h x y := by
  intro r hr
  rcases Set.uIcc_subset_uIcc_union_uIcc hr with hr | hr
  · exact h1 r hr
  · exact h2 r hr

lemma good_neg (Q : Matrix (Fin n) (Fin n) ℝ) (h : (Fin n → ℝ) → ℝ) (heven : ∀ x, h (-x) = h x)
    (x y : Fin n → ℝ) (hg : Good Q h x (-y)) : Good Q h x y := by
  intro r hr; rw [← heven y] at hr; exact hg r hr

lemma good_link0 (Q : Matrix (Fin n) (Fin n) ℝ) (h : (Fin n → ℝ) → ℝ)
    (hh : ContinuousOn h {x | x ≠ 0}) (heven : ∀ x, h (-x) = h x)
    (x y : Fin n → ℝ) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : qf Q x = 0) (hy : qf Q y = 0)
    (hb : bf Q x y = 0) : Good Q h x y := by
  have seg : ∀ y' : Fin n → ℝ, qf Q y' = 0 → bf Q x y' = 0 →
      (∀ θ ∈ Set.Icc (0:ℝ) 1, (1 - θ) • x + θ • y' ≠ 0) → Good Q h x y' := by
    intro y' hy' hb' hne
    have := good_path Q h hh (fun θ => (1 - θ) • x + θ • y' + (0:ℝ) • y') (by fun_prop)
      (fun θ hθ => by simpa using hne θ hθ)
      (fun θ _ => by rw [qf3, hx, hy', hb']; ring)
    simpa using this
  by_cases hs : ∀ θ ∈ Set.Icc (0:ℝ) 1, (1 - θ) • x + θ • y ≠ 0
  · exact seg y hy hb hs
  · apply good_neg Q h heven
    apply seg (-y) (by rw [qf_neg, hy]) (by rw [bf_neg, hb, neg_zero])
    push Not at hs
    obtain ⟨θ, ⟨h0, h1⟩, he⟩ := hs
    intro θ' ⟨h0', h1'⟩ he'
    have key : (θ' * (1 - θ) + θ * (1 - θ')) • x = 0 := by
      have : (θ' * (1 - θ) + θ * (1 - θ')) • x
          = θ' • ((1 - θ) • x + θ • y) + θ • ((1 - θ') • x + θ' • -y) := by module
      rw [this, he, he']; simp
    rcases smul_eq_zero.mp key with hk | hk
    · have hp1 : 0 ≤ θ' * (1 - θ) := mul_nonneg h0' (by linarith)
      have hp2 : 0 ≤ θ * (1 - θ') := mul_nonneg h0 (by linarith)
      have ha : θ' * (1 - θ) = 0 := by linarith
      have hb2 : θ * (1 - θ') = 0 := by linarith
      by_cases hθ0 : θ = 0
      · subst hθ0; simp at he; exact hx0 he
      · have hθ'1 : θ' = 1 := by
          rcases mul_eq_zero.mp hb2 with h | h
          · exact absurd h hθ0
          · linarith
        subst hθ'1
        have hθ1 : θ = 1 := by
          rcases mul_eq_zero.mp ha with h | h
          · norm_num at h
          · linarith
        subst hθ1
        simp at he; exact hy0 he
    · exact hx0 hk

lemma good_link_c (Q : Matrix (Fin n) (Fin n) ℝ) (h : (Fin n → ℝ) → ℝ)
    (hh : ContinuousOn h {x | x ≠ 0})
    (x y : Fin n → ℝ) (hx : qf Q x = 0) (hy : qf Q y = 0)
    (w : Fin n → ℝ) (hxw : bf Q x w = 0) (hyw : bf Q y w = 0) (hbc : bf Q x y * qf Q w < 0) :
    Good Q h x y := by
  set b := bf Q x y with hbdef
  set c := qf Q w with hcdef
  have hb : b ≠ 0 := by rintro h; rw [h, zero_mul] at hbc; exact lt_irrefl _ hbc
  have hc : c ≠ 0 := by rintro h; rw [h, mul_zero] at hbc; exact lt_irrefl _ hbc
  have hk : 0 ≤ -b / c := by
    have : -b / c = -(b * c) / c ^ 2 := by field_simp
    rw [this]; exact div_nonneg (by linarith) (sq_nonneg _)
  have := good_path Q h hh (fun θ => (1 - θ) • x + θ • y
      + Real.sqrt (θ * (1 - θ) * (-b / c)) • w) (by fun_prop)
    (by
      intro θ hθ h0
      have e1 := congrArg (bf Q x) h0
      have e2 := congrArg (bf Q y) h0
      rw [bf_lin, bf_zero, bf_self, hx, hxw] at e1
      rw [bf_lin, bf_zero, bf_self, hy, hyw, bf_comm Q y x] at e2
      have h1 : θ * b = 0 := by linarith
      have h2 : (1 - θ) * b = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h | h
      · rw [h] at h2; simp at h2; exact hb h2
      · exact hb h)
    (by
      intro θ hθ
      rcases hθ with ⟨h0, h1⟩
      rw [qf3, hx, hy, hxw, hyw, ← hbdef, ← hcdef,
        Real.sq_sqrt (mul_nonneg (mul_nonneg h0 (by linarith)) hk)]
      field_simp
      ring)
  simpa using this

lemma exists_w (hn : 3 ≤ n) (Q : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    ∃ w : Fin n → ℝ, w ≠ 0 ∧ bf Q x w = 0 ∧ bf Q y w = 0 := by
  let fL : (Fin n → ℝ) → ((Fin n → ℝ) →ₗ[ℝ] ℝ) := fun z =>
    { toFun := fun w => bf Q z w
      map_add' := fun u w => by simpa using bf_lin Q 1 1 0 z u w w
      map_smul' := fun a u => by simpa using bf_smul Q a z u }
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.pi ![fL x, fL y]
  have hlt : Module.finrank ℝ (Fin 2 → ℝ) < Module.finrank ℝ (Fin n → ℝ) := by
    simp; omega
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt hlt)
  refine ⟨w, hw0, ?_, ?_⟩
  · have := congrFun ((LinearMap.mem_ker (f := L)).mp hw) 0
    simpa [L, fL] using this
  · have := congrFun ((LinearMap.mem_ker (f := L)).mp hw) 1
    simpa [L, fL] using this

/-- Core: for `n ≥ 3`, an even function continuous off `0` takes on the punctured cone
`qf Q = 0` every value between its values at two points of the cone. -/
lemma good_link (hn : 3 ≤ n) (Q : Matrix (Fin n) (Fin n) ℝ) (h : (Fin n → ℝ) → ℝ)
    (hh : ContinuousOn h {x | x ≠ 0}) (heven : ∀ x, h (-x) = h x)
    (x y : Fin n → ℝ) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : qf Q x = 0) (hy : qf Q y = 0) :
    Good Q h x y := by
  by_cases hb : bf Q x y = 0
  · exact good_link0 Q h hh heven x y hx0 hy0 hx hy hb
  obtain ⟨w, hw0, hxw, hyw⟩ := exists_w hn Q x y
  rcases lt_trichotomy (bf Q x y * qf Q w) 0 with hl | hl | hl
  · exact good_link_c Q h hh x y hx hy w hxw hyw hl
  · have hc : qf Q w = 0 := by
      rcases mul_eq_zero.mp hl with h | h
      · exact absurd h hb
      · exact h
    exact good_trans Q h x w y (good_link0 Q h hh heven x w hx0 hw0 hx hc hxw)
      (good_link0 Q h hh heven w y hw0 hy0 hc hy (by rw [bf_comm]; exact hyw))
  · apply good_neg Q h heven
    exact good_link_c Q h hh x (-y) hx (by rw [qf_neg, hy]) w hxw
      (by rw [bf_comm, bf_neg, bf_comm, hyw, neg_zero]) (by rw [bf_neg]; linarith)

end PC101


open Matrix Filter

namespace PC101

variable {n : ℕ}

def FF (A : Fin 3 → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin 3 → ℝ :=
  fun i => x ⬝ᵥ (A i *ᵥ x)

lemma dot_FF (A : Fin 3 → Matrix (Fin n) (Fin n) ℝ) (a : Fin 3 → ℝ) (x : Fin n → ℝ) :
    a ⬝ᵥ FF A x = qf (∑ i, a i • A i) x := by
  unfold FF qf
  simp only [Fin.sum_univ_three, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  simp [dotProduct, Fin.sum_univ_three]

lemma FF_smul (A : Fin 3 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    FF A (t • x) = t ^ 2 • FF A x := by
  funext i
  simp only [FF, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Pi.smul_apply]
  ring

lemma FF_neg (A : Fin 3 → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : FF A (-x) = FF A x := by
  simpa using FF_smul A (-1) x

lemma FF_zero (A : Fin 3 → Matrix (Fin n) (Fin n) ℝ) : FF A 0 = 0 := by
  simpa using FF_smul A 0 0

lemma FF_cont (A : Fin 3 → Matrix (Fin n) (Fin n) ℝ) : Continuous (FF A) := by
  unfold FF; fun_prop

lemma qf_cont (Q : Matrix (Fin n) (Fin n) ℝ) : Continuous (qf Q) := by
  unfold qf; fun_prop

lemma det_line (c p q : Fin 3 → ℝ) (hp : c ⬝ᵥ p = 1) (hq : c ⬝ᵥ q = 1) :
    (Matrix.of ![c, p ⨯₃ q, q - p]).det = -((q - p) ⬝ᵥ (q - p)) := by
  rw [Matrix.det_fin_three]
  simp only [cross_apply, dotProduct, Fin.sum_univ_three] at *
  simp
  linear_combination (p 0 * (q 0 - p 0) + p 1 * (q 1 - p 1) + p 2 * (q 2 - p 2)) * hq
    - (q 0 * (q 0 - p 0) + q 1 * (q 1 - p 1) + q 2 * (q 2 - p 2)) * hp

/-- Brickman-type step: the normalized image is convex. -/
lemma conv_step (hn : 3 ≤ n) (A : Fin 3 → Matrix (Fin n) (Fin n) ℝ) (c : Fin 3 → ℝ)
    (hpd : (∑ i, c i • A i).PosDef) (x1 x2 : Fin n → ℝ) (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0)
    (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ∃ e, e ≠ 0 ∧ (qf (∑ i, c i • A i) e)⁻¹ • FF A e =
      μ • ((qf (∑ i, c i • A i) x1)⁻¹ • FF A x1)
        + (1 - μ) • ((qf (∑ i, c i • A i) x2)⁻¹ • FF A x2) := by
  set M := ∑ i, c i • A i with hMdef
  have mpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < qf M x := by
    intro x hx
    have := hpd.dotProduct_mulVec_pos hx
    simpa [qf] using this
  set p := (qf M x1)⁻¹ • FF A x1 with hpdef
  set q := (qf M x2)⁻¹ • FF A x2 with hqdef
  have hcp : c ⬝ᵥ p = 1 := by
    rw [hpdef, dotProduct_smul, dot_FF, smul_eq_mul, inv_mul_cancel₀ (mpos x1 hx1).ne']
  have hcq : c ⬝ᵥ q = 1 := by
    rw [hqdef, dotProduct_smul, dot_FF, smul_eq_mul, inv_mul_cancel₀ (mpos x2 hx2).ne']
  by_cases hpq : p = q
  · refine ⟨x1, hx1, ?_⟩
    rw [← hpdef, ← hpq]; module
  set d := q - p with hddef
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have hdd : 0 < d ⬝ᵥ d := by
    have : 0 < star d ⬝ᵥ d := dotProduct_star_self_pos_iff.mpr hd
    simpa using this
  set av := p ⨯₃ q with havdef
  set Q := ∑ i, av i • A i with hQdef
  let h : (Fin n → ℝ) → ℝ := fun x => d ⬝ᵥ ((qf M x)⁻¹ • FF A x - p)
  have hh : ContinuousOn h {x | x ≠ 0} := by
    have hc : Continuous fun z : Fin 3 → ℝ => d ⬝ᵥ (z - p) := by fun_prop
    exact hc.comp_continuousOn (ContinuousOn.smul
      (((qf_cont M).continuousOn).inv₀ (fun x hx => (mpos x hx).ne')) (FF_cont A).continuousOn)
  have heven : ∀ x, h (-x) = h x := by
    intro x; simp only [h, FF_neg, qf_neg]
  have hQ1 : qf Q x1 = 0 := by
    rw [hQdef, ← dot_FF]
    have : FF A x1 = qf M x1 • p := by rw [hpdef, smul_smul, mul_inv_cancel₀ (mpos x1 hx1).ne', one_smul]
    rw [this, dotProduct_smul, havdef, dotProduct_comm, dot_self_cross]; simp
  have hQ2 : qf Q x2 = 0 := by
    rw [hQdef, ← dot_FF]
    have : FF A x2 = qf M x2 • q := by rw [hqdef, smul_smul, mul_inv_cancel₀ (mpos x2 hx2).ne', one_smul]
    rw [this, dotProduct_smul, havdef, dotProduct_comm, dot_cross_self]; simp
  have hgood := good_link hn Q h hh heven x1 x2 hx1 hx2 hQ1 hQ2
  have h1 : h x1 = 0 := by show d ⬝ᵥ ((qf M x1)⁻¹ • FF A x1 - p) = 0; rw [← hpdef, sub_self, dotProduct_zero]
  have h2 : h x2 = d ⬝ᵥ d := by simp only [h, ← hqdef, hddef]
  obtain ⟨e, he0, hQe, hhe⟩ := hgood ((1 - μ) * (d ⬝ᵥ d)) (by
    rw [h1, h2, Set.uIcc_of_le hdd.le]
    exact ⟨mul_nonneg (by linarith) hdd.le, by nlinarith⟩)
  refine ⟨e, he0, ?_⟩
  set z := (qf M e)⁻¹ • FF A e with hzdef
  have hcz : c ⬝ᵥ z = 1 := by
    rw [hzdef, dotProduct_smul, dot_FF, smul_eq_mul, inv_mul_cancel₀ (mpos e he0).ne']
  have haz : av ⬝ᵥ z = 0 := by
    rw [hzdef, dotProduct_smul, dot_FF, ← hQdef, hQe]; simp
  have hdz : d ⬝ᵥ (z - p) = (1 - μ) * (d ⬝ᵥ d) := hhe
  have hu : z - (μ • p + (1 - μ) • q) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero (M := Matrix.of ![c, av, d])
    · rw [havdef, hddef, det_line c p q hcp hcq]
      exact neg_ne_zero.mpr (by rw [← hddef]; exact hdd.ne')
    · funext i
      fin_cases i
      · simp [mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, hcz, hcp, hcq]
      · have hap : av ⬝ᵥ p = 0 := by rw [havdef, dotProduct_comm]; exact dot_self_cross p q
        have haq : av ⬝ᵥ q = 0 := by rw [havdef, dotProduct_comm]; exact dot_cross_self p q
        simp only [dotProduct, Fin.sum_univ_three] at haz hap haq
        simp [mulVec, dotProduct, Fin.sum_univ_three]
        linear_combination haz - μ * hap - (1 - μ) * haq
      · have : d ⬝ᵥ (z - (μ • p + (1 - μ) • q)) = 0 := by
          have e1 : z - (μ • p + (1 - μ) • q) = (z - p) - (1 - μ) • d := by rw [hddef]; module
          rw [e1, dotProduct_sub, hdz, dotProduct_smul, smul_eq_mul, sub_self]
        simpa [mulVec] using this
  exact sub_eq_zero.mp hu

end PC101


open Matrix Filter

namespace PC101

variable {n : ℕ}

lemma closed_range (hn : 3 ≤ n) (A : Fin 3 → Matrix (Fin n) (Fin n) ℝ) (c : Fin 3 → ℝ)
    (hpd : (∑ i, c i • A i).PosDef) : IsClosed (Set.range (FF A)) := by
  set M := ∑ i, c i • A i with hMdef
  have mpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < qf M x := by
    intro x hx
    have := hpd.dotProduct_mulVec_pos hx
    simpa [qf] using this
  -- lower bound `qf M x ≥ λ ‖x‖²`
  have hne : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty := by
    have : Nontrivial (Fin n → ℝ) := by
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      infer_instance
    exact NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hne
    (qf_cont M).continuousOn
  have hx00 : x0 ≠ 0 := by
    rintro rfl; simp at hx0
  set lam := qf M x0 with hlam
  have hlam0 : 0 < lam := mpos x0 hx00
  have hlow : ∀ x, lam * ‖x‖ ^ 2 ≤ qf M x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [qf]
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hs : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
      simp [norm_smul, hxn.ne']
    have := hmin hs
    simp only [Set.mem_ofPred_eq, qf_smul] at this
    have e : qf M x = ‖x‖ ^ 2 * ((‖x‖⁻¹) ^ 2 * qf M x) := by field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left this (sq_nonneg ‖x‖)
    linarith [this, show lam * ‖x‖ ^ 2 = ‖x‖ ^ 2 * lam by ring]
  -- upper bound `qf M x ≤ C ‖F x‖`
  set C := ∑ i, |c i| + 1 with hC
  have hC0 : 0 < C := by positivity
  have hup : ∀ x, qf M x ≤ C * ‖FF A x‖ := by
    intro x
    rw [← dot_FF]
    calc c ⬝ᵥ FF A x ≤ ∑ i, |c i| * ‖FF A x‖ := by
          unfold dotProduct
          apply Finset.sum_le_sum
          intro i _
          calc c i * FF A x i ≤ |c i * FF A x i| := le_abs_self _
            _ = |c i| * |FF A x i| := abs_mul _ _
            _ ≤ |c i| * ‖FF A x‖ := mul_le_mul_of_nonneg_left
                (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (FF A x) i) (abs_nonneg _)
      _ = (∑ i, |c i|) * ‖FF A x‖ := by rw [Finset.sum_mul]
      _ ≤ C * ‖FF A x‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          linarith
  have hprop : IsProperMap (FF A) := by
    rw [isProperMap_iff_tendsto_cocompact]
    refine ⟨FF_cont A, ?_⟩
    rw [← Metric.cobounded_eq_cocompact, ← Metric.cobounded_eq_cocompact,
      ← tendsto_norm_atTop_iff_cobounded]
    have ht : Tendsto (fun x : Fin n → ℝ => lam / C * ‖x‖ ^ 2) (Bornology.cobounded _) atTop :=
      Tendsto.const_mul_atTop (div_pos hlam0 hC0)
        ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop)
    refine tendsto_atTop_mono (fun x => ?_) ht
    rw [div_mul_eq_mul_div, div_le_iff₀ hC0]
    linarith [hlow x, hup x, mul_comm C ‖FF A x‖]
  rw [← Set.image_univ]
  exact hprop.isClosedMap _ isClosed_univ

lemma convex_range (hn : 3 ≤ n) (A : Fin 3 → Matrix (Fin n) (Fin n) ℝ) (c : Fin 3 → ℝ)
    (hpd : (∑ i, c i • A i).PosDef) : Convex ℝ (Set.range (FF A)) := by
  set M := ∑ i, c i • A i with hMdef
  have mpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < qf M x := by
    intro x hx
    have := hpd.dotProduct_mulVec_pos hx
    simpa [qf] using this
  rintro _ ⟨x1, rfl⟩ _ ⟨x2, rfl⟩ a b ha hb hab
  by_cases hx1 : x1 = 0
  · subst hx1
    refine ⟨Real.sqrt b • x2, ?_⟩
    rw [FF_smul, FF_zero, Real.sq_sqrt hb]; simp
  by_cases hx2 : x2 = 0
  · subst hx2
    refine ⟨Real.sqrt a • x1, ?_⟩
    rw [FF_smul, FF_zero, Real.sq_sqrt ha]; simp
  set m1 := qf M x1
  set m2 := qf M x2
  have hm1 : 0 < m1 := mpos x1 hx1
  have hm2 : 0 < m2 := mpos x2 hx2
  set τ := a * m1 + b * m2 with hτ
  have hτ0 : 0 < τ := by
    rcases eq_or_lt_of_le ha with h | h
    · subst h; simp at hab; subst hab; simp [hτ]; exact hm2
    · have := mul_pos h hm1; have := mul_nonneg hb hm2.le; linarith
  set μ := a * m1 / τ with hμ
  have hμ0 : 0 ≤ μ := div_nonneg (mul_nonneg ha hm1.le) hτ0.le
  have hμ1 : μ ≤ 1 := by
    rw [hμ, div_le_one hτ0]; have := mul_nonneg hb hm2.le; linarith
  obtain ⟨e, he0, he⟩ := conv_step hn A c hpd x1 x2 hx1 hx2 μ hμ0 hμ1
  have hme : 0 < qf M e := mpos e he0
  refine ⟨Real.sqrt (τ / qf M e) • e, ?_⟩
  rw [FF_smul, Real.sq_sqrt (div_nonneg hτ0.le hme.le)]
  have e2 : (τ / qf M e) • FF A e = τ • ((qf M e)⁻¹ • FF A e) := by
    rw [smul_smul, div_eq_mul_inv]
  rw [e2, he]
  have h1μ : 1 - μ = b * m2 / τ := by
    rw [hμ]; field_simp; linarith
  rw [h1μ, hμ, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  · congr 1; show τ * (a * m1 / τ) * m1⁻¹ = a; field_simp
  · congr 1; show τ * (b * m2 / τ) * m2⁻¹ = b; field_simp

end PC101

open PC101 in
theorem solution {n : ℕ} (hn : 3 ≤ n) (A : Fin 3 → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hpd : ∃ c : Fin 3 → ℝ, (∑ i, c i • A i).PosDef) :
    IsClosed (Set.range fun x : Fin n → ℝ => fun i => x ⬝ᵥ (A i *ᵥ x)) ∧
      Convex ℝ (Set.range fun x : Fin n → ℝ => fun i => x ⬝ᵥ (A i *ᵥ x)) := by
  obtain ⟨c, hc⟩ := hpd
  exact ⟨closed_range hn A c hc, convex_range hn A c hc⟩
