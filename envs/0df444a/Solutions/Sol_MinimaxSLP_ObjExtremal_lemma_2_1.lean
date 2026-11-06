-- Prove2me | solution 1 for MinimaxSLP.ObjExtremal.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:15:01.795577+00:00
-- url     : https://prove2.me/submissions/946e240f-b339-4f1b-8816-4ece7c0782f8

import Mathlib
import Definitions.Def_MinimaxSLP_ObjExtremal_Model
import Theorems.Thm_MinimaxSLP_ObjExtremal_scaled_weak_duality
import Theorems.Thm_MinimaxSLP_ObjExtremal_jensen_step
import Theorems.Thm_MinimaxSLP_ObjExtremal_dual9_attained
import Theorems.Thm_MinimaxSLP_ObjExtremal_theorem_2_2

open MeasureTheory Matrix

namespace MSLP2L21
open MinimaxSLP.ObjSDP MinimaxSLP.ObjExtremal

lemma bordered_quad {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (v0 : ℝ)
    (z : Fin d → ℝ) (c : ℝ) :
    star (Sum.elim z (fun _ : Fin 1 => c)) ⬝ᵥ (bordered V v v0 *ᵥ Sum.elim z (fun _ => c)) =
      z ⬝ᵥ (V *ᵥ z) + 2 * c * (z ⬝ᵥ v) + c ^ 2 * v0 := by
  simp only [star_trivial, bordered, dotProduct, mulVec, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, of_apply,
    Fin.sum_univ_one]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  have : ∀ i, ∑ j, z i * (V i j * z j) = ∑ j, z i * V i j * z j := fun i =>
    Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => this i]
  have e1 : ∑ i, z i * (v i * c) = ∑ i, c * (z i * v i) := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, c * (v i * z i) = ∑ i, c * (z i * v i) := Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  simp only [← Finset.mul_sum]
  ring
lemma bordered_add {d : ℕ} (V V' : Matrix (Fin d) (Fin d) ℝ) (v v' : Fin d → ℝ) (c c' : ℝ) :
    bordered (V + V') (v + v') (c + c') = bordered V v c + bordered V' v' c' := by
  ext (i | i) (j | j) <;> simp [bordered]

lemma bordered_smul {d : ℕ} (θ : ℝ) (V : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (c : ℝ) :
    bordered (θ • V) (θ • v) (θ * c) = θ • bordered V v c := by
  ext (i | i) (j | j) <;> simp [bordered]

lemma bordered_zero {d : ℕ} : bordered (0 : Matrix (Fin d) (Fin d) ℝ) 0 0 = 0 := by
  ext (i | i) (j | j) <;> simp [bordered]

lemma Mbar_posDef {d : ℕ} (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm)
    (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef) : (bordered Q μ 1).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [bordered, conjTranspose_apply, Fin.fin_one_eq_zero]
    exact congrFun (congrFun hQ a) b
  · intro y hy
    have hy' : y = Sum.elim (fun a => y (Sum.inl a)) (fun _ : Fin 1 => y (Sum.inr 0)) := by
      funext a; rcases a with a | a
      · rfl
      · simp [Fin.fin_one_eq_zero a]
    rw [hy', bordered_quad]
    set z : Fin d → ℝ := fun a => y (Sum.inl a)
    set c := y (Sum.inr 0)
    have e : z ⬝ᵥ (Q *ᵥ z) = z ⬝ᵥ ((Q - vecMulVec μ μ) *ᵥ z) + (z ⬝ᵥ μ) ^ 2 := by
      rw [sub_mulVec, dotProduct_sub, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul,
        smul_eq_mul, dotProduct_comm μ z]
      ring
    rw [e]
    by_cases hz : z = 0
    · have hc : c ≠ 0 := by
        intro hc; apply hy; rw [hy']; funext a; rcases a with a | a
        · simp only [Sum.elim_inl]; exact congrFun hz a
        · simp [hc]
      rw [hz]; simp; positivity
    · have := hA4.dotProduct_mulVec_pos hz
      simp only [star_trivial] at this
      nlinarith [sq_nonneg (z ⬝ᵥ μ + c)]
lemma U_cont {K : ℕ} [NeZero K] (α β : Fin K → ℝ) : Continuous (disutility α β) := by
  unfold disutility
  exact Continuous.finset_sup'_apply _ fun k _ => by fun_prop

lemma U_bound {K : ℕ} [NeZero K] (α β : Fin K → ℝ) (t : ℝ) :
    |disutility α β t| ≤ ∑ k, (|α k| * |t| + |β k|) := by
  have hk : ∀ k, |α k * t + β k| ≤ ∑ k, (|α k| * |t| + |β k|) := by
    intro k
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    exact Finset.single_le_sum (f := fun k => |α k| * |t| + |β k|)
      (fun k _ => by positivity) (Finset.mem_univ k)
  rw [abs_le]
  constructor
  · have h1 : α 0 * t + β 0 ≤ disutility α β t :=
      Finset.le_sup' (fun k => α k * t + β k) (Finset.mem_univ 0)
    have := neg_abs_le (α 0 * t + β 0)
    linarith [hk 0]
  · exact Finset.sup'_le _ _ fun k _ => (le_abs_self _).trans (hk k)


lemma feas9_comb {r d K : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (α : Fin K → ℝ) (μ : Fin d → ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ)
    (s s' : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ))
    (hs : s ∈ feasible9 W α μ Q) (hs' : s' ∈ feasible9 W α μ Q) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ • s + (1 - θ) • s' ∈ feasible9 W α μ Q := by
  obtain ⟨hsum, hp, hd⟩ := hs
  obtain ⟨hsum', hp', hd'⟩ := hs'
  have h1' : 0 ≤ 1 - θ := by linarith
  refine ⟨?_, fun k => ?_, fun k => ?_⟩
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, bordered_add, bordered_smul, Finset.sum_add_distrib,
      ← Finset.smul_sum, hsum, hsum']
    rw [← add_smul]; simp
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, bordered_add, bordered_smul]
    exact ((hp k).smul h0).add ((hp' k).smul h1')
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, mulVec_add, mulVec_smul, smul_add]
    rw [smul_comm (α k) θ, smul_comm (α k) (1 - θ)]
    exact add_le_add (smul_le_smul_of_nonneg_left (hd k) h0)
      (smul_le_smul_of_nonneg_left (hd' k) h1')

lemma obj9_comb {n r d K : ℕ} (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ) (β : Fin K → ℝ)
    (x : Fin n → ℝ)
    (s s' : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ)) (θ : ℝ) :
    obj9 T h β x (θ • s + (1 - θ) • s') = θ * obj9 T h β x s + (1 - θ) * obj9 T h β x s' := by
  simp only [obj9, Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
    Pi.smul_apply, dotProduct_add,
    dotProduct_smul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem l21_main {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty)
    (hmax : ∃ s ∈ feasible9 W α μ Q, ∀ s' ∈ feasible9 W α μ Q, obj9 T h β x s' ≤ obj9 T h β x s)
    (hZ : ∀ P ∈ momentClass μ Q, ∀ s ∈ feasible9 W α μ Q,
      (∀ s' ∈ feasible9 W α μ Q, obj9 T h β x s' ≤ obj9 T h β x s) →
      ∫ q, disutility α β (Qval W T h q x) ∂P ≤ obj9 T h β x s)
    (P : Measure (Fin d → ℝ)) (hP : P ∈ momentClass μ Q) :
    Integrable (fun q => disutility α β (Qval W T h q x)) P ∧
      ∃ s ∈ feasible9 W α μ Q, ∫ q, disutility α β (Qval W T h q x) ∂P = obj9 T h β x s := by
  classical
  have hP0 := hP
  obtain ⟨⟨hprob, hmem⟩, hmean, -⟩ := hP
  haveI := hprob
  have hint : ∀ i, Integrable (fun ξ : Fin d → ℝ => ξ i) P := fun i => (hmem i).integrable one_le_two
  have hQint := (jensen_step W T h hA3 x hrec P hint).1
  have hUint : Integrable (fun q => disutility α β (Qval W T h q x)) P := by
    refine Integrable.mono' (g := fun q => ∑ k, (|α k| * |Qval W T h q x| + |β k|)) ?_
      ((U_cont α β).comp_aestronglyMeasurable hQint.1)
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact U_bound α β _)
    exact integrable_finsetSum _ fun k _ => (hQint.abs.const_mul _).add (integrable_const _)
  refine ⟨hUint, ?_⟩
  set E := ∫ q, disutility α β (Qval W T h q x) ∂P with hE
  -- a feasible point of (9) with value at most `E`
  choose πp hπp using fun i : Fin d => hA3 (Pi.single i 1)
  choose πm hπm using fun i : Fin d => hA3 (-Pi.single i 1)
  set a : Fin d → ℝ := fun i => ∫ q, max (q i) 0 ∂P with ha
  set b : Fin d → ℝ := fun i => ∫ q, max (-q i) 0 ∂P with hb
  have ha0 : ∀ i, 0 ≤ a i := fun i => integral_nonneg fun q => le_max_right _ _
  have hb0 : ∀ i, 0 ≤ b i := fun i => integral_nonneg fun q => le_max_right _ _
  have hab : ∀ i, a i - b i = μ i := by
    intro i
    rw [ha, hb, ← integral_sub (hint i).pos_part (hint i).neg_part, ← congrFun hmean i]
    simp only [MomentDRO.Conf.meanVec]
    congr 1; funext q
    rcases le_total 0 (q i) with hq | hq
    · rw [max_eq_left hq, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hq, max_eq_left (by linarith)]; ring
  set c := h - T *ᵥ x with hc
  set p : Fin r → ℝ := α 0 • ∑ i, (a i • πp i + b i • πm i) with hp
  set slow : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ) := (fun k => if k = 0 then Q else 0, fun k => if k = 0 then μ else 0,
        fun k => if k = 0 then 1 else 0, fun k => if k = 0 then p else 0) with hslow
  have hWp : Wᵀ *ᵥ (∑ i, (a i • πp i + b i • πm i)) ≤ μ := by
    have : Wᵀ *ᵥ (∑ i, (a i • πp i + b i • πm i)) ≤
        ∑ i, (a i • (Pi.single i (1 : ℝ)) + b i • (-Pi.single i (1 : ℝ))) := by
      rw [mulVec_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mulVec_add, mulVec_smul, mulVec_smul]
      exact add_le_add (smul_le_smul_of_nonneg_left (hπp i) (ha0 i))
        (smul_le_smul_of_nonneg_left (hπm i) (hb0 i))
    refine this.trans (le_of_eq ?_)
    funext j
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib]
    linarith [hab j]
  have hslowF : slow ∈ feasible9 W α μ Q := by
    refine ⟨?_, fun k => ?_, fun k => ?_⟩
    · rw [Fintype.sum_eq_single 0]
      · simp [slow]
      · intro k hk; simp [slow, hk, bordered_zero]
    · by_cases hk : k = 0
      · simp only [slow, hk, if_true]; exact (Mbar_posDef μ Q hQ hA4).posSemidef
      · simp only [slow, hk, if_false, bordered_zero]; exact PosSemidef.zero
    · by_cases hk : k = 0
      · subst hk; simp only [slow, if_true, hp, mulVec_smul]
        exact smul_le_smul_of_nonneg_left hWp (hα 0)
      · simp [slow, hk]
  have hslowv : obj9 T h β x slow ≤ E := by
    have hobj : obj9 T h β x slow = α 0 * ∑ i, (a i * (c ⬝ᵥ πp i) + b i * (c ⬝ᵥ πm i)) + β 0 := by
      simp only [obj9]
      rw [Fintype.sum_eq_single 0]
      · simp only [slow, if_true, hp, ← hc, dotProduct_smul, dotProduct_sum, dotProduct_add,
          smul_eq_mul, mul_one]
      · intro k hk; simp [slow, hk]
    -- pointwise: the piecewise-linear dual selection
    have hpt : ∀ q : Fin d → ℝ,
        α 0 * ∑ i, (max (q i) 0 * (c ⬝ᵥ πp i) + max (-q i) 0 * (c ⬝ᵥ πm i)) + β 0 ≤
          disutility α β (Qval W T h q x) := by
      intro q
      have hW : Wᵀ *ᵥ (∑ i, (max (q i) 0 • πp i + max (-q i) 0 • πm i)) ≤ (1 : ℝ) • q := by
        rw [one_smul, mulVec_sum]
        have : q = ∑ i, (max (q i) 0 • Pi.single i (1 : ℝ) + max (-q i) 0 • (-Pi.single i (1 : ℝ))) := by
          funext j
          simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
            Pi.single_apply, mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_add_distrib,
            Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib]
          rcases le_total 0 (q j) with hq | hq
          · rw [max_eq_left hq, max_eq_right (by linarith)]; ring
          · rw [max_eq_right hq, max_eq_left (by linarith)]; ring
        conv_rhs => rw [this]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mulVec_add, mulVec_smul, mulVec_smul]
        exact add_le_add (smul_le_smul_of_nonneg_left (hπp i) (le_max_right _ _))
          (smul_le_smul_of_nonneg_left (hπm i) (le_max_right _ _))
      have hwd := scaled_weak_duality W T h hA3 x hrec 1 zero_le_one q _ hW
      rw [one_mul, ← hc, dotProduct_sum] at hwd
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hwd
      have hU : α 0 * Qval W T h q x + β 0 ≤ disutility α β (Qval W T h q x) :=
        Finset.le_sup' (fun k => α k * Qval W T h q x + β k) (Finset.mem_univ 0)
      have := mul_le_mul_of_nonneg_left hwd (hα 0)
      linarith
    have hint2 : Integrable (fun q : Fin d → ℝ =>
        α 0 * ∑ i, (max (q i) 0 * (c ⬝ᵥ πp i) + max (-q i) 0 * (c ⬝ᵥ πm i)) + β 0) P :=
      ((integrable_finsetSum _ fun i _ => ((hint i).pos_part.mul_const _).add
        ((hint i).neg_part.mul_const _)).const_mul _).add (integrable_const _)
    have hmono := integral_mono hint2 hUint hpt
    have hFi : ∀ i, Integrable (fun q : Fin d → ℝ =>
        max (q i) 0 * (c ⬝ᵥ πp i) + max (-q i) 0 * (c ⬝ᵥ πm i)) P :=
      fun i => ((hint i).pos_part.mul_const _).add ((hint i).neg_part.mul_const _)
    have e3 : ∀ i, ∫ q, (max (q i) 0 * (c ⬝ᵥ πp i) + max (-q i) 0 * (c ⬝ᵥ πm i)) ∂P =
        a i * (c ⬝ᵥ πp i) + b i * (c ⬝ᵥ πm i) := by
      intro i
      rw [integral_add (f := fun q : Fin d → ℝ => max (q i) 0 * (c ⬝ᵥ πp i))
        (g := fun q : Fin d → ℝ => max (-q i) 0 * (c ⬝ᵥ πm i))
        ((hint i).pos_part.mul_const _) ((hint i).neg_part.mul_const _),
        integral_mul_const, integral_mul_const]
    have e2 : ∫ q, (∑ i, (max (q i) 0 * (c ⬝ᵥ πp i) + max (-q i) 0 * (c ⬝ᵥ πm i))) ∂P =
        ∑ i, (a i * (c ⬝ᵥ πp i) + b i * (c ⬝ᵥ πm i)) := by
      rw [integral_finsetSum _ fun i _ => hFi i]
      exact Finset.sum_congr rfl fun i _ => e3 i
    have e1 : ∫ q, (α 0 * ∑ i, (max (q i) 0 * (c ⬝ᵥ πp i) + max (-q i) 0 * (c ⬝ᵥ πm i)) + β 0) ∂P =
        α 0 * ∑ i, (a i * (c ⬝ᵥ πp i) + b i * (c ⬝ᵥ πm i)) + β 0 := by
      rw [integral_add (f := fun q : Fin d → ℝ =>
        α 0 * ∑ i, (max (q i) 0 * (c ⬝ᵥ πp i) + max (-q i) 0 * (c ⬝ᵥ πm i)))
        (g := fun _ => β 0) ((integrable_finsetSum _ fun i _ => hFi i).const_mul _)
        (integrable_const _), integral_const_mul, e2, integral_const]
      simp
    rw [hobj, ← e1]
    exact hmono
  -- an optimal point of (9) has value at least `E`
  obtain ⟨sh, hshF, hshmax⟩ := hmax
  have hshv : E ≤ obj9 T h β x sh := hZ P hP0 sh hshF hshmax
  -- interpolate
  rcases eq_or_lt_of_le (hslowv.trans hshv) with heq | hlt
  · refine ⟨slow, hslowF, le_antisymm (by linarith) hslowv⟩
  · set θ := (obj9 T h β x sh - E) / (obj9 T h β x sh - obj9 T h β x slow) with hθ
    have hden : 0 < obj9 T h β x sh - obj9 T h β x slow := by linarith
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hden.le
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hden]; linarith
    refine ⟨θ • slow + (1 - θ) • sh, feas9_comb W α μ Q slow sh hslowF hshF θ hθ0 hθ1, ?_⟩
    rw [obj9_comb, hθ]
    field_simp
    ring

end MSLP2L21

open MinimaxSLP.ObjExtremal in
theorem solution {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty) :
    (∀ P ∈ MinimaxSLP.ObjSDP.momentClass μ Q,
      Integrable (fun q => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.ObjSDP.Qval W T h q x)) P ∧
      ∃ s ∈ feasible9 W α μ Q, ∫ q, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.ObjSDP.Qval W T h q x) ∂P = obj9 T h β x s) ∧
    MinimaxSLP.ObjSDP.Zx W T h α β μ Q x ≤ ZDD W T h α β μ Q x := by
  obtain ⟨-, hlub, -, hlub9, hZD, hZDD⟩ :=
    theorem_2_2 A b W T h α β hα μ Q hQ hA4 hA3 x hx hrec
  have hmax := dual9_attained A b W T h α β hα μ Q hQ hA4 hA3 x hx hrec
  refine ⟨fun P hP => MSLP2L21.l21_main W T h α β hα μ Q hQ hA4 hA3 x hrec hmax ?_ P hP, ?_⟩
  · intro P' hP' s hs hsmax
    have h1 := hlub.1 ⟨P', hP', rfl⟩
    have h2 : ZDD W T h α β μ Q x ≤ obj9 T h β x s :=
      hlub9.2 (by rintro _ ⟨s', hs', rfl⟩; exact hsmax s' hs')
    simp only at h1
    linarith
  · rw [hZD, hZDD]
