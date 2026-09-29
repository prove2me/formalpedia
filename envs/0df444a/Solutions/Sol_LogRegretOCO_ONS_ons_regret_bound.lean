-- Prove2me | solution 1 for LogRegretOCO.ONS.ons_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T15:07:51.114468+00:00
-- url     : https://prove2.me/submissions/ad273fb3-8a51-40a3-8d27-423937a52a44

import Theorems.Thm_LogRegretOCO_ONS_exp_concave_quadratic_lower_bound
import Theorems.Thm_LogRegretOCO_ONS_gen_proj_ineq
import Theorems.Thm_LogRegretOCO_ONS_elliptical_potential
import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic
import Definitions.Def_LogRegretOCO_ONS_Run

open Matrix
open scoped RealInnerProductSpace

namespace LogRegretOCO.ONS

variable {n : ℕ}

lemma inner_eq_dot (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪a, b⟫ = WithLp.ofLp a ⬝ᵥ WithLp.ofLp b := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma quadForm_add (A B : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    quadForm (A + B) v = quadForm A v + quadForm B v := by
  simp [quadForm, add_mulVec, dotProduct_add]

lemma quadForm_vecMulVec (g : Fin n → ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    quadForm (vecMulVec g g) v = (g ⬝ᵥ WithLp.ofLp v) ^ 2 := by
  unfold quadForm
  set w := WithLp.ofLp v
  have : vecMulVec g g *ᵥ w = (g ⬝ᵥ w) • g := by
    ext i
    simp only [vecMulVec, mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, dotProduct_smul, smul_eq_mul, dotProduct_comm w g]; ring

lemma quadForm_smul_one (ε : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    quadForm (ε • (1 : Matrix (Fin n) (Fin n) ℝ)) v = ε * ‖v‖ ^ 2 := by
  unfold quadForm
  rw [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, ← inner_eq_dot,
    real_inner_self_eq_norm_sq]

lemma quadForm_sum (s : Finset ℕ) (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    quadForm (∑ i ∈ s, A i) v = ∑ i ∈ s, quadForm (A i) v := by
  unfold quadForm
  rw [sum_mulVec, dotProduct_sum]

lemma regGram_quad (ε : ℝ) (u : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    quadForm (regGram ε u t) v =
      ∑ τ ∈ Finset.Icc 1 t, (WithLp.ofLp (u τ) ⬝ᵥ WithLp.ofLp v) ^ 2 + ε * ‖v‖ ^ 2 := by
  unfold regGram
  rw [quadForm_add, quadForm_sum, quadForm_smul_one]
  simp only [quadForm_vecMulVec]

lemma regGram_succ (ε : ℝ) (u : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    regGram ε u (t + 1) = regGram ε u t +
      vecMulVec (WithLp.ofLp (u (t + 1))) (WithLp.ofLp (u (t + 1))) := by
  unfold regGram
  rw [Finset.sum_Icc_succ_top (by omega)]
  abel

lemma regGram_symm (ε : ℝ) (u : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    (regGram ε u t)ᵀ = regGram ε u t := by
  unfold regGram
  rw [transpose_add, transpose_sum, transpose_smul, transpose_one]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [transpose_vecMulVec]

lemma regGram_det (ε : ℝ) (hε : 0 < ε) (u : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    IsUnit (regGram ε u t).det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_zero_iff).2 h
  have hq := regGram_quad ε u t (WithLp.toLp 2 v)
  have hq0 : quadForm (regGram ε u t) (WithLp.toLp 2 v) = 0 := by
    simp [quadForm, hv]
  rw [hq0] at hq
  have hs : 0 ≤ ∑ τ ∈ Finset.Icc 1 t, (WithLp.ofLp (u τ) ⬝ᵥ WithLp.ofLp (WithLp.toLp 2 v)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hn : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; intro h'; apply hv0
    have := congrArg WithLp.ofLp h'; simpa using this
  have : 0 < ε * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by positivity
  linarith

lemma quadForm_nonneg (ε : ℝ) (hε : 0 ≤ ε) (u : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ)
    (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ quadForm (regGram ε u t) v := by
  rw [regGram_quad]
  have : 0 ≤ ∑ τ ∈ Finset.Icc 1 t, (WithLp.ofLp (u τ) ⬝ᵥ WithLp.ofLp v) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

/-- expansion of the quadratic form at the Newton step -/
lemma quad_step (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (hdet : IsUnit A.det)
    (w g : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    quadForm A (w - c • WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp g)) =
      quadForm A w - 2 * c * ⟪g, w⟫ + c ^ 2 * quadForm A⁻¹ g := by
  have hAh : A *ᵥ (A⁻¹ *ᵥ WithLp.ofLp g) = WithLp.ofLp g := by
    rw [mulVec_mulVec, mul_nonsing_inv A hdet, one_mulVec]
  have hsym : ∀ a b : Fin n → ℝ, a ⬝ᵥ (A *ᵥ b) = b ⬝ᵥ (A *ᵥ a) := fun a b => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]
  unfold quadForm
  simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, WithLp.ofLp_toLp]
  set a := WithLp.ofLp w
  set h := A⁻¹ *ᵥ WithLp.ofLp g
  rw [inner_eq_dot]
  rw [mulVec_sub, mulVec_smul, hAh, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct]
  have e1 : h ⬝ᵥ WithLp.ofLp g = WithLp.ofLp g ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp g) := dotProduct_comm _ _
  have e2 : h ⬝ᵥ (A *ᵥ a) = a ⬝ᵥ WithLp.ofLp g := by rw [← hsym, hAh]
  rw [e1, e2, dotProduct_comm a (WithLp.ofLp g)]
  simp only [smul_eq_mul]; ring

theorem ons_potential_main (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP_conv : Convex ℝ P)
    (G D α : ℝ) (hG : 0 < G) (hD : 0 < D) (hα : 0 < α)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ∀ t, ∀ x ∈ P, DifferentiableAt ℝ (f t) x)
    (hgrad : ∀ t, ∀ x ∈ P, ‖gradient (f t) x‖ ≤ G)
    (hexp : ∀ t, ConcaveOn ℝ P (fun x => Real.exp (-α * f t x)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsONSRun P G D α f x) (T : ℕ) :
    ∀ u ∈ P, ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤
      1 / (2 * onsBeta G D α) *
          ∑ t ∈ Finset.Icc 1 T, quadForm (onsMatrix G D α f x t)⁻¹ (gradient (f t) (x t)) +
        1 / (2 * onsBeta G D α) := by
  intro u hu
  set β := onsBeta G D α with hβ
  set ε := onsEps G D α with hεdef
  have hβpos : 0 < β := by
    rw [hβ, onsBeta]; apply mul_pos (by norm_num); apply lt_min _ hα; positivity
  have hεpos : 0 < ε := by rw [hεdef, onsEps]; positivity
  set gr : ℕ → EuclideanSpace ℝ (Fin n) := fun i => gradient (f i) (x i) with hgr
  have hA : ∀ t, onsMatrix G D α f x t = regGram ε gr t := fun t => rfl
  have hxP : ∀ t, 1 ≤ t → x t ∈ P := by
    intro t ht
    induction t with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact hrun.1
      · exact (hrun.2 k hk).1
  set Q : ℕ → ℝ := fun t => quadForm (regGram ε gr t) (x (t + 1) - u) with hQ
  -- one step
  have step : ∀ t, 1 ≤ t →
      f t (x t) - f t u ≤ 1 / (2 * β) * quadForm (regGram ε gr t)⁻¹ (gr t) +
        β / 2 * (Q (t - 1) - Q t) := by
    intro t ht
    have hxt := hxP t ht
    -- exp-concavity
    have hlow := exp_concave_quadratic_lower_bound P G D α β hG hD hdiam (f t) (hdiff t)
      (hgrad t) (hexp t) hβpos (le_of_eq rfl) u hu (x t) hxt
    set s := ⟪gr t, x t - u⟫ with hs
    have hs' : ⟪gradient (f t) (x t), u - x t⟫ = -s := by
      rw [hs, ← inner_neg_right, neg_sub]
    rw [hs', neg_sq] at hlow
    -- projection
    have hpsd : (regGram ε gr t).PosSemidef := by
      refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v => ?_⟩
      · unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact regGram_symm ε gr t
      · have := quadForm_nonneg ε hεpos.le gr t (WithLp.toLp 2 v)
        simpa [quadForm] using this
    have hproj := gen_proj_ineq P hP_conv (onsMatrix G D α f x t) hpsd _ _ (hrun.2 t ht) u hu
    rw [hA] at hproj
    have ey : x t - (1 / onsBeta G D α) •
        WithLp.toLp 2 ((regGram ε gr t)⁻¹ *ᵥ WithLp.ofLp (gradient (f t) (x t))) - u =
        (x t - u) - (1 / β) • WithLp.toLp 2 ((regGram ε gr t)⁻¹ *ᵥ WithLp.ofLp (gr t)) := by
      rw [← hβ]; simp only [hgr]; abel
    rw [ey, quad_step _ (regGram_symm ε gr t) (regGram_det ε hεpos gr t)] at hproj
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    have hsplit : quadForm (regGram ε gr (k + 1)) (x (k + 1) - u) = Q k + s ^ 2 := by
      rw [regGram_succ, quadForm_add, quadForm_vecMulVec, hs, inner_eq_dot]
    rw [hsplit] at hproj
    have hQt : Q (k + 1) = quadForm (regGram ε gr (k + 1)) (x (k + 1 + 1) - u) := rfl
    rw [← hQt] at hproj
    simp only [Nat.add_sub_cancel]
    set qi := quadForm (regGram ε gr (k + 1))⁻¹ (gr (k + 1))
    have hm := mul_le_mul_of_nonneg_left hproj (by positivity : (0 : ℝ) ≤ β / 2)
    have e : β / 2 * (Q k + s ^ 2 - 2 * (1 / β) * s + (1 / β) ^ 2 * qi) =
        β / 2 * Q k + β / 2 * s ^ 2 - s + 1 / (2 * β) * qi := by field_simp
    rw [e] at hm
    have e2 : β / 2 * (Q k - Q (k + 1)) = β / 2 * Q k - β / 2 * Q (k + 1) := by ring
    rw [e2]
    linarith
  -- telescoping
  have hind : ∀ T', ∑ t ∈ Finset.Icc 1 T', (f t (x t) - f t u) + β / 2 * Q T' ≤
      1 / (2 * β) * ∑ t ∈ Finset.Icc 1 T', quadForm (regGram ε gr t)⁻¹ (gr t) + β / 2 * Q 0 := by
    intro T'
    induction T' with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have hs := step (k + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hs
      rw [mul_add]
      linarith
  have h1 := hind T
  have hQT : 0 ≤ Q T := quadForm_nonneg ε hεpos.le gr T _
  have hQ0 : Q 0 ≤ ε * D ^ 2 := by
    have e : Q 0 = ε * ‖x 1 - u‖ ^ 2 := by
      show quadForm (regGram ε gr 0) (x (0 + 1) - u) = _
      rw [regGram_quad]; simp
    rw [e]
    have := hdiam (x 1) hrun.1 u hu
    have : ‖x 1 - u‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    exact mul_le_mul_of_nonneg_left this hεpos.le
  have hconst : β / 2 * (ε * D ^ 2) = 1 / (2 * β) := by
    rw [hεdef, onsEps, ← hβ]; field_simp
  have : β / 2 * Q 0 ≤ 1 / (2 * β) := by
    rw [← hconst]; exact mul_le_mul_of_nonneg_left hQ0 (by positivity)
  have : 0 ≤ β / 2 * Q T := by positivity
  show _ ≤ 1 / (2 * β) * ∑ t ∈ Finset.Icc 1 T, quadForm (regGram ε gr t)⁻¹ (gr t) + 1 / (2 * β)
  linarith


theorem ons_goal_main (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP_conv : Convex ℝ P)
    (G D α : ℝ) (hG : 0 < G) (hD : 0 < D) (hα : 0 < α)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ∀ t, ∀ x ∈ P, DifferentiableAt ℝ (f t) x)
    (hgrad : ∀ t, ∀ x ∈ P, ‖gradient (f t) x‖ ≤ G)
    (hexp : ∀ t, ConcaveOn ℝ P (fun x => Real.exp (-α * f t x)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsONSRun P G D α f x)
    (T : ℕ) (hT : 4 ≤ (n : ℝ) * Real.log T) :
    ∀ u ∈ P, ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤
      5 * (1 / α + G * D) * n * Real.log T := by
  intro u hu
  have hpot := ons_potential_main P hP_conv G D α hG hD hα hdiam f hdiff hgrad hexp x hrun T u hu
  set β := onsBeta G D α with hβ
  set ε := onsEps G D α with hεdef
  have hβpos : 0 < β := by
    rw [hβ, onsBeta]; apply mul_pos (by norm_num); apply lt_min _ hα; positivity
  have hεpos : 0 < ε := by rw [hεdef, onsEps]; positivity
  set gr : ℕ → EuclideanSpace ℝ (Fin n) := fun i => gradient (f i) (x i) with hgr
  have hxP : ∀ t, 1 ≤ t → x t ∈ P := by
    intro t ht
    induction t with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact hrun.1
      · exact (hrun.2 k hk).1
  have hell := elliptical_potential gr G ε hG hεpos T
    (fun t ht => hgrad t (x t) (hxP t (Finset.mem_Icc.1 ht).1))
  have hsum : ∑ t ∈ Finset.Icc 1 T, quadForm (onsMatrix G D α f x t)⁻¹ (gradient (f t) (x t)) =
      ∑ t ∈ Finset.Icc 1 T, quadForm (regGram ε gr t)⁻¹ (gr t) := rfl
  rw [hsum] at hpot
  -- T ≥ 2
  have hT2 : (2 : ℝ) ≤ T := by
    rcases Nat.lt_or_ge T 2 with h | h
    · interval_cases T <;> simp at hT <;> linarith
    · exact_mod_cast h
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hn : (0 : ℝ) < n := by
    by_contra h; push_neg at h
    have : (n : ℝ) * Real.log T ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hL.le
    linarith
  -- the logarithm
  have hβGD : β * (G * D) ≤ 1 / 8 := by
    have h1 : β ≤ 1 / 2 * (1 / (4 * G * D)) := by
      rw [hβ, onsBeta]; exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ G * D)
    have e : 1 / 2 * (1 / (4 * G * D)) * (G * D) = 1 / 8 := by field_simp; ring
    linarith
  have harg : G ^ 2 * T / ε + 1 ≤ T := by
    have e : G ^ 2 * T / ε = (β * (G * D)) ^ 2 * T := by
      rw [hεdef, onsEps, ← hβ]; field_simp
    rw [e]
    have h0 : 0 ≤ β * (G * D) := by positivity
    have : (β * (G * D)) ^ 2 ≤ 1 / 64 := by nlinarith
    have hT0 : (0 : ℝ) ≤ T := by linarith
    nlinarith
  have hlog : Real.log (G ^ 2 * T / ε + 1) ≤ Real.log T :=
    Real.log_le_log (by positivity) harg
  have hK : 0 < 1 / (2 * β) := by positivity
  have hKb : 1 / (2 * β) ≤ 4 * G * D + 1 / α := by
    have e : 2 * β = min (1 / (4 * G * D)) α := by rw [hβ, onsBeta]; ring
    rw [e]
    rcases min_choice (1 / (4 * G * D)) α with h | h
    · rw [h]; field_simp; have : 0 < 1 / α := by positivity
      nlinarith [this]
    · rw [h]; have : 0 < 4 * G * D := by positivity
      linarith
  have h1 : ∑ t ∈ Finset.Icc 1 T, quadForm (regGram ε gr t)⁻¹ (gr t) ≤ n * Real.log T :=
    hell.trans (mul_le_mul_of_nonneg_left hlog hn.le)
  have h2 : 1 / (2 * β) * ∑ t ∈ Finset.Icc 1 T, quadForm (regGram ε gr t)⁻¹ (gr t) +
      1 / (2 * β) ≤ 1 / (2 * β) * (5 / 4 * (n * Real.log T)) := by
    have := mul_le_mul_of_nonneg_left h1 hK.le
    nlinarith
  have h3 : 1 / (2 * β) * (5 / 4 * (n * Real.log T)) ≤
      (4 * G * D + 1 / α) * (5 / 4 * (n * Real.log T)) :=
    mul_le_mul_of_nonneg_right hKb (by positivity)
  have h4 : (4 * G * D + 1 / α) * (5 / 4 * (n * Real.log T)) ≤
      5 * (1 / α + G * D) * n * Real.log T := by
    have : 0 < 1 / α * (n * Real.log T) := by positivity
    nlinarith
  linarith

end LogRegretOCO.ONS

open LogRegretOCO.ONS

theorem solution {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP_ne : P.Nonempty) (hP_closed : IsClosed P) (hP_bdd : Bornology.IsBounded P)
    (hP_conv : Convex ℝ P)
    (G D α : ℝ) (hG : 0 < G) (hD : 0 < D) (hα : 0 < α)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ∀ t, ∀ x ∈ P, DifferentiableAt ℝ (f t) x)
    (hgrad : ∀ t, ∀ x ∈ P, ‖gradient (f t) x‖ ≤ G)
    (hexp : ∀ t, ConcaveOn ℝ P (fun x => Real.exp (-α * f t x)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsONSRun P G D α f x)
    (T : ℕ) (hT : 4 ≤ (n : ℝ) * Real.log T) :
    ∀ u ∈ P, ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤
      5 * (1 / α + G * D) * n * Real.log T := by
  exact ons_goal_main P hP_conv G D α hG hD hα hdiam f hdiff hgrad hexp x hrun T hT
