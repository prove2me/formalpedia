-- Prove2me | solution 1 for MinimaxSLP.ObjExtremal.strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:05:46.142534+00:00
-- url     : https://prove2.me/submissions/c1db1e2b-7fe5-4f06-887b-42ca5c083734

import Mathlib
import Definitions.Def_MinimaxSLP_ObjExtremal_Model
import Theorems.Thm_MinimaxSLP_ObjExtremal_jensen_step
import Theorems.Thm_MinimaxSLP_ObjExtremal_feasible9_approx
import Theorems.Thm_MinimaxSLP_ObjExtremal_dual6_le_dual9_upper

open MeasureTheory Matrix

namespace MSLP2SD
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

lemma Qval_le {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (w0 : Fin d → ℝ) (hw0 : w0 ∈ recourseSet W T h x) (ρ : Fin d → ℝ) :
    Qval W T h ρ x ≤ ρ ⬝ᵥ w0 := by
  obtain ⟨π, hπ⟩ := hA3 ρ
  apply csInf_le
  · refine ⟨(h - T *ᵥ x) ⬝ᵥ π, ?_⟩
    rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
    have e1 : (h - T *ᵥ x) ⬝ᵥ π = (Wᵀ *ᵥ π) ⬝ᵥ w := by
      rw [← hw1, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    rw [e1]
    exact dotProduct_le_dotProduct_of_nonneg_right hπ hw2
  · exact ⟨w0, hw0, rfl⟩

/-- weak duality between the moment problem (5) and its dual (6) -/
lemma weak6 {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty)
    (P : Measure (Fin d → ℝ)) (hP : P ∈ momentClass μ Q)
    (s : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ) (hs : s ∈ dualFeasible6 W T h α β x) :
    Integrable (fun q => disutility α β (Qval W T h q x)) P ∧
    ∫ q, disutility α β (Qval W T h q x) ∂P ≤ frob Q s.1 + μ ⬝ᵥ s.2.1 + s.2.2 := by
  obtain ⟨⟨hprob, hmem⟩, hmean, hsec⟩ := hP
  haveI := hprob
  have hint : ∀ i, Integrable (fun ξ : Fin d → ℝ => ξ i) P := fun i => (hmem i).integrable one_le_two
  have hQint := (jensen_step W T h hA3 x hrec P hint).1
  have hUint : Integrable (fun q => disutility α β (Qval W T h q x)) P := by
    refine Integrable.mono' (g := fun q => ∑ k, (|α k| * |Qval W T h q x| + |β k|)) ?_
      ((U_cont α β).comp_aestronglyMeasurable hQint.1)
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact U_bound α β _)
    exact integrable_finsetSum _ fun k _ => (hQint.abs.const_mul _).add (integrable_const _)
  have hmul : ∀ a b, Integrable (fun ξ : Fin d → ℝ => ξ a * ξ b) P :=
    fun a b => (hmem a).integrable_mul (hmem b)
  obtain ⟨Y, y, y0⟩ := s
  obtain ⟨-, hfe⟩ := hs
  simp only at hfe ⊢
  set Yf : Fin d → Fin d → ℝ := fun a b => Y a b with hYf
  have hquad : ∀ q : Fin d → ℝ, q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y0 =
      ∑ a, ∑ b, Yf a b * (q a * q b) + ∑ a, y a * q a + y0 := by
    intro q
    simp only [dotProduct, mulVec, Finset.mul_sum]
    congr 2
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    · exact Finset.sum_congr rfl fun a _ => by ring
  have hqi : Integrable (fun q : Fin d → ℝ => ∑ a, ∑ b, Yf a b * (q a * q b) + ∑ a, y a * q a + y0) P := by
    refine ((integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (hmul a b).const_mul _).add (integrable_finsetSum _ fun a _ => (hint a).const_mul _)).add
      (integrable_const _)
  refine ⟨hUint, ?_⟩
  calc ∫ q, disutility α β (Qval W T h q x) ∂P
      ≤ ∫ q, (∑ a, ∑ b, Yf a b * (q a * q b) + ∑ a, y a * q a + y0) ∂P := by
        refine integral_mono hUint hqi fun q => ?_
        rw [← hquad]; exact hfe q
    _ = frob Q Y + μ ⬝ᵥ y + y0 := by
        have iA : Integrable (fun q : Fin d → ℝ => ∑ a, ∑ b, Yf a b * (q a * q b)) P :=
          integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hmul a b).const_mul _
        have iB : Integrable (fun q : Fin d → ℝ => ∑ a, y a * q a) P :=
          integrable_finsetSum _ fun a _ => (hint a).const_mul _
        rw [integral_add (f := fun q : Fin d → ℝ => ∑ a, ∑ b, Yf a b * (q a * q b) + ∑ a, y a * q a)
          (g := fun _ => y0) (iA.add iB) (integrable_const _),
          integral_add (f := fun q : Fin d → ℝ => ∑ a, ∑ b, Yf a b * (q a * q b))
          (g := fun q : Fin d → ℝ => ∑ a, y a * q a) iA iB,
          integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hmul a b).const_mul _,
          integral_finsetSum _ fun a _ => (hint a).const_mul _, integral_const]
        simp only [probReal_univ, one_smul]
        have h2 : ∀ a b, ∫ q, Yf a b * (q a * q b) ∂P = Yf a b * Q a b := by
          intro a b
          rw [integral_const_mul]
          have := congrFun (congrFun hsec a) b
          simp only [MomentDRO.Conf.secondMomentAbout, of_apply, Pi.zero_apply, sub_zero] at this
          rw [this]
        have h1 : ∀ a, ∫ q, y a * q a ∂P = y a * μ a := by
          intro a
          rw [integral_const_mul]
          have := congrFun hmean a
          simp only [MomentDRO.Conf.meanVec] at this
          rw [this]
        simp only [h1, frob, dotProduct]
        rw [Finset.sum_congr rfl fun a _ => integral_finsetSum _ fun b _ => (hmul a b).const_mul _]
        simp only [h2]
        congr 1
        congr 1
        · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
        · exact Finset.sum_congr rfl fun a _ => by ring

end MSLP2SD

open MinimaxSLP.ObjExtremal in
theorem solution {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty) :
    IsLUB (MinimaxSLP.ObjSDP.primalValues W T h α β μ Q x) (MinimaxSLP.ObjSDP.Zx W T h α β μ Q x) ∧
    IsGLB (MinimaxSLP.ObjSDP.dualValues6 W T h α β μ Q x) (MinimaxSLP.ObjSDP.ZD W T h α β μ Q x) ∧
    MinimaxSLP.ObjSDP.Zx W T h α β μ Q x = MinimaxSLP.ObjSDP.ZD W T h α β μ Q x := by
  classical
  open MinimaxSLP.ObjSDP MSLP2SD in
  obtain ⟨w0, hw0⟩ := hrec
  have hrec : (recourseSet W T h x).Nonempty := ⟨w0, hw0⟩
  -- an explicit feasible point of (6)
  set c : ℝ := ∑ k, |β k + α k ^ 2 * (w0 ⬝ᵥ w0) / 4| with hc
  have h6 : ((1 : Matrix (Fin d) (Fin d) ℝ), (0 : Fin d → ℝ), c) ∈ dualFeasible6 W T h α β x := by
    refine ⟨by simp [IsSymm], fun q => ?_⟩
    simp only [one_mulVec, dotProduct_zero, add_zero]
    apply Finset.sup'_le
    intro k _
    have h1 := Qval_le W T h hA3 x w0 hw0 q
    have h2 : α k * Qval W T h q x ≤ α k * (q ⬝ᵥ w0) := mul_le_mul_of_nonneg_left h1 (hα k)
    have e : ∑ i, (q i - α k / 2 * w0 i) ^ 2 =
        q ⬝ᵥ q - α k * (q ⬝ᵥ w0) + α k ^ 2 / 4 * (w0 ⬝ᵥ w0) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h3 : 0 ≤ ∑ i, (q i - α k / 2 * w0 i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h4 : β k + α k ^ 2 * (w0 ⬝ᵥ w0) / 4 ≤ c :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun k => |β k + α k ^ 2 * (w0 ⬝ᵥ w0) / 4|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ k))
    nlinarith
  -- an explicit feasible point of (9)
  obtain ⟨π0, hπ0⟩ := hA3 μ
  set s9 : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ) := (fun k => if k = 0 then Q else 0, fun k => if k = 0 then μ else 0,
        fun k => if k = 0 then 1 else 0, fun k => if k = 0 then α 0 • π0 else 0)
  have h9 : s9 ∈ feasible9 W α μ Q := by
    refine ⟨?_, fun k => ?_, fun k => ?_⟩
    · rw [Fintype.sum_eq_single 0]
      · simp [s9]
      · intro k hk; simp [s9, hk, MSLP2SD.bordered_zero]
    · by_cases hk : k = 0
      · simp only [s9, hk, if_true]; exact (MSLP2SD.Mbar_posDef μ Q hQ hA4).posSemidef
      · simp only [s9, hk, if_false, MSLP2SD.bordered_zero]; exact PosSemidef.zero
    · by_cases hk : k = 0
      · subst hk; simp only [s9, if_true, mulVec_smul]
        exact smul_le_smul_of_nonneg_left hπ0 (hα 0)
      · simp [s9, hk]
  -- weak duality, nonemptiness, boundedness
  have hweak : ∀ a ∈ primalValues W T h α β μ Q x, ∀ b ∈ dualValues6 W T h α β μ Q x, a ≤ b := by
    rintro _ ⟨P, hP, rfl⟩ _ ⟨s, hs, rfl⟩
    exact (MSLP2SD.weak6 W T h α β μ Q hA3 x hrec P hP s hs).2
  obtain ⟨P0, hP0, -, -⟩ := feasible9_approx W T h α β hα μ Q hA3 x hrec s9 h9 1 one_pos
  have hne : (primalValues W T h α β μ Q x).Nonempty := ⟨_, P0, hP0, rfl⟩
  have hne6 : (dualValues6 W T h α β μ Q x).Nonempty := ⟨_, _, h6, rfl⟩
  have hbdd : BddAbove (primalValues W T h α β μ Q x) :=
    ⟨_, fun a ha => hweak a ha _ hne6.some_mem⟩
  have hbdd6 : BddBelow (dualValues6 W T h α β μ Q x) :=
    ⟨_, fun b hb => hweak _ hne.some_mem b hb⟩
  have hlub : IsLUB (primalValues W T h α β μ Q x) (Zx W T h α β μ Q x) := isLUB_csSup hne hbdd
  have hglb : IsGLB (dualValues6 W T h α β μ Q x) (ZD W T h α β μ Q x) := isGLB_csInf hne6 hbdd6
  refine ⟨hlub, hglb, le_antisymm ?_ ?_⟩
  · exact csSup_le hne fun a ha => le_csInf hne6 fun b hb => hweak a ha b hb
  · -- `Z(x)` bounds (9), and (6) comes within any `ε` of such a bound
    have hub9 : Zx W T h α β μ Q x ∈ upperBounds (dualValues9 W T h α β μ Q x) := by
      rintro _ ⟨s, hs, rfl⟩
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      obtain ⟨P', hP', -, hb⟩ := feasible9_approx W T h α β hα μ Q hA3 x hrec s hs δ hδ
      have := hlub.1 ⟨P', hP', rfl⟩
      linarith
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨s, hs, hv⟩ := dual6_le_dual9_upper W T h α β hα μ Q hQ hA4 hA3 x hrec _ hub9 ε hε
    exact (csInf_le hbdd6 ⟨s, hs, rfl⟩).trans hv
