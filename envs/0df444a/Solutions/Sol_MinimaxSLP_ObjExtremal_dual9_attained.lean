-- Prove2me | solution 1 for MinimaxSLP.ObjExtremal.dual9_attained
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:10:29.265204+00:00
-- url     : https://prove2.me/submissions/3f57c2d0-ad97-49a5-bfcd-283cb71e5795

import Mathlib
import Definitions.Def_MinimaxSLP_ObjExtremal_Model
import Theorems.Thm_MinimaxSLP_ObjExtremal_Qval_homogeneous_superadditive
import Theorems.Thm_MinimaxSLP_ObjExtremal_scaled_weak_duality
import Theorems.Thm_LP_strong_duality_matrix

open MeasureTheory Matrix

namespace MSLP2Att
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
/-- LP attainment: `𝒬(q, x)` is the attained maximum of its dual. -/
lemma Qval_dual_attained {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) (q : Fin d → ℝ) :
    ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q ∧ (h - T *ᵥ x) ⬝ᵥ π = Qval W T h q x := by
  obtain ⟨w0, hw01, hw02⟩ := hrec
  obtain ⟨π, y, hπ, hy0, hy, hval, -⟩ := LP.strong_duality_matrix Wᵀ q (h - T *ᵥ x) (hA3 q)
    ⟨w0, hw02, by rw [transpose_transpose, hw01]⟩
  refine ⟨π, hπ, le_antisymm ?_ ?_⟩
  · have := scaled_weak_duality W T h hA3 x ⟨w0, hw01, hw02⟩ 1 zero_le_one q π (by simpa using hπ)
    simpa using this
  · rw [hval]
    apply csInf_le
    · refine ⟨(h - T *ᵥ x) ⬝ᵥ π, ?_⟩
      rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
      have e1 : (h - T *ᵥ x) ⬝ᵥ π = (Wᵀ *ᵥ π) ⬝ᵥ w := by
        rw [← hw1, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
      rw [e1]
      exact dotProduct_le_dotProduct_of_nonneg_right hπ hw2
    · refine ⟨y, ⟨?_, hy0⟩, rfl⟩
      rw [transpose_transpose] at hy
      exact hy
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

lemma Qval_continuous {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) :
    Continuous (fun q => Qval W T h q x) := by
  obtain ⟨hhom, hsup⟩ := Qval_homogeneous_superadditive W T h hA3 x hrec
  have hconc : ConcaveOn ℝ Set.univ (fun q => Qval W T h q x) := by
    refine ⟨convex_univ, fun a _ b _ l m hl hm hlm => ?_⟩
    rcases hl.lt_or_eq with hl | hl
    · rcases hm.lt_or_eq with hm | hm
      · have := hsup (l • a) (m • b)
        rw [hhom l hl, hhom m hm] at this
        simpa [smul_eq_mul] using this
      · subst hm
        have : l = 1 := by linarith
        subst this; simp
    · subst hl
      have : m = 1 := by linarith
      subst this; simp
  exact continuousOn_univ.mp (hconc.continuousOn isOpen_univ)

def quadF {ι : Type} [Fintype ι] (A : ι → ι → ℝ) (y : ι → ℝ) : ℝ := ∑ a, ∑ b, y a * A a b * y b

lemma quadF_eq {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (y : ι → ℝ) :
    quadF (fun a b => A a b) y = star y ⬝ᵥ (A *ᵥ y) := by
  simp only [quadF, star_trivial, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma psd_iff_fun {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) :
    A.PosSemidef ↔ (∀ a b, A a b = A b a) ∧ ∀ y, 0 ≤ quadF (fun a b => A a b) y := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨hH, hq⟩
    refine ⟨fun a b => ?_, fun y => by rw [quadF_eq]; exact hq y⟩
    have := congrFun (congrFun hH a) b
    simpa [conjTranspose_apply] using this.symm
  · rintro ⟨hs, hq⟩
    refine ⟨?_, fun y => by rw [← quadF_eq]; exact hq y⟩
    ext a b; simp [conjTranspose_apply, hs b a]

lemma quadF_two {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → ι → ℝ) (a b : ι) (t : ℝ) :
    quadF A (Pi.single a 1 + t • Pi.single b 1) = A a a + t * A a b + t * A b a + t ^ 2 * A b b := by
  have e : ∀ i j : ι, Pi.single i (1 : ℝ) ⬝ᵥ ((Matrix.of A) *ᵥ Pi.single j 1) = A i j := by
    intro i j; simp [mulVec, dotProduct, Pi.single_apply]
  have := quadF_eq (Matrix.of A) (Pi.single a 1 + t • Pi.single b 1)
  simp only [of_apply] at this
  rw [this, star_trivial, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
    dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_dotProduct, e, e, e, e]
  simp only [smul_eq_mul]
  ring

theorem att_main {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) :
    ∃ s ∈ feasible9 W α μ Q, ∀ s' ∈ feasible9 W α μ Q, obj9 T h β x s' ≤ obj9 T h β x s := by
  classical
  set Mb : (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ := fun a b => bordered Q μ 1 a b with hMb
  set Fs : Set (Fin K → (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ) :=
    {M | (∀ k a b, M k a b = M k b a) ∧ (∀ k y, 0 ≤ quadF (M k) y) ∧
      ∀ a b, ∑ k, M k a b = Mb a b} with hFs
  set g : (Fin K → (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ) → ℝ :=
    fun M => ∑ k, (α k * Qval W T h (fun a => M k (Sum.inl a) (Sum.inr 0)) x +
      β k * M k (Sum.inr 0) (Sum.inr 0)) with hg
  have hQc := Qval_continuous W T h hA3 x hrec
  have hgc : Continuous g := by
    refine continuous_finset_sum _ fun k _ => ?_
    refine (continuous_const.mul (hQc.comp ?_)).add (continuous_const.mul ?_)
    · exact continuous_pi fun a => (continuous_apply _).comp ((continuous_apply _).comp
        (continuous_apply k))
    · exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply k))
  -- the feasible set of blocks is compact
  set R : ℝ := ∑ a, |Mb a a| with hR
  have hbound : ∀ M ∈ Fs, ∀ k a b, M k a b ∈ Set.Icc (-R) R := by
    rintro M ⟨hs, hq, hsum⟩ k a b
    have hdiag : ∀ k a, 0 ≤ M k a a := by
      intro k a
      have := quadF_two (M k) a a 0
      simp only [zero_smul, add_zero, zero_mul, sq, mul_zero] at this
      have h2 := hq k (Pi.single a 1)
      linarith
    have hdle : ∀ k a, M k a a ≤ R := by
      intro k a
      have h1 : M k a a ≤ Mb a a := by
        rw [← hsum a a]
        exact Finset.single_le_sum (f := fun k => M k a a) (fun k _ => hdiag k a)
          (Finset.mem_univ k)
      have h2 : Mb a a ≤ R := (le_abs_self _).trans
        (Finset.single_le_sum (f := fun a => |Mb a a|) (fun a _ => abs_nonneg _) (Finset.mem_univ a))
      linarith
    have hp := hq k (Pi.single a 1 + (1 : ℝ) • Pi.single b 1)
    have hm := hq k (Pi.single a 1 + (-1 : ℝ) • Pi.single b 1)
    rw [quadF_two] at hp hm
    have hsab := hs k a b
    have := hdiag k a; have := hdiag k b; have := hdle k a; have := hdle k b
    constructor <;> nlinarith
  have hclosed : IsClosed Fs := by
    have e : Fs = (⋂ k, ⋂ a, ⋂ b, {M : Fin K → (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ |
        M k a b = M k b a}) ∩ ((⋂ k, ⋂ y, {M : Fin K → (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ |
        0 ≤ quadF (M k) y}) ∩ (⋂ a, ⋂ b, {M : Fin K → (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ |
        ∑ k, M k a b = Mb a b})) := by
      ext M; simp [hFs]
    rw [e]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun k => isClosed_iInter fun a => isClosed_iInter fun b =>
        isClosed_eq (by fun_prop) (by fun_prop)
    · refine isClosed_iInter fun k => isClosed_iInter fun y => isClosed_le continuous_const ?_
      simp only [quadF]
      fun_prop
    · exact isClosed_iInter fun a => isClosed_iInter fun b =>
        isClosed_eq (by fun_prop) continuous_const
  have hcpt : IsCompact Fs := by
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ => isCompact_Icc (a := -R) (b := R)) hclosed ?_
    intro M hM
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    exact hbound M hM
  -- nonempty
  have hMbsym : ∀ a b, Mb a b = Mb b a := by
    intro a b
    rcases a with a | a <;> rcases b with b | b <;> simp [hMb, bordered, Fin.fin_one_eq_zero]
    exact congrFun (congrFun hQ b) a
  have hMbpsd := (psd_iff_fun _).mp (Mbar_posDef μ Q hQ hA4).posSemidef
  have hne : Fs.Nonempty := by
    refine ⟨fun k => if k = 0 then Mb else 0, fun k a b => ?_, fun k y => ?_, fun a b => ?_⟩
    · by_cases hk : k = 0 <;> simp [hk, hMbsym a b]
    · by_cases hk : k = 0
      · simp only [hk, if_true]; exact hMbpsd.2 y
      · simp [hk, quadF]
    · rw [Fintype.sum_eq_single 0]
      · simp
      · intro k hk; simp [hk]
  obtain ⟨Ms, hMs, hmax⟩ := hcpt.exists_isMaxOn hne hgc.continuousOn
  obtain ⟨hs1, hs2, hs3⟩ := hMs
  -- the optimal solution
  set V : Fin K → Matrix (Fin d) (Fin d) ℝ := fun k => Matrix.of fun a b => Ms k (Sum.inl a) (Sum.inl b)
  set v : Fin K → Fin d → ℝ := fun k a => Ms k (Sum.inl a) (Sum.inr 0)
  set v0 : Fin K → ℝ := fun k => Ms k (Sum.inr 0) (Sum.inr 0)
  choose π hπ hπv using fun k => Qval_dual_attained W T h hA3 x hrec (v k)
  have hbord : ∀ k, ∀ a b, bordered (V k) (v k) (v0 k) a b = Ms k a b := by
    intro k a b
    rcases a with a | a <;> rcases b with b | b
    · simp [bordered, V]
    · simp [bordered, v, Fin.fin_one_eq_zero b]
    · simp only [bordered, fromBlocks_apply₂₁, of_apply, v, Fin.fin_one_eq_zero a]
      exact hs1 k _ _
    · simp [bordered, v0, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
  have hfeas : (V, v, v0, fun k => α k • π k) ∈ feasible9 W α μ Q := by
    refine ⟨?_, fun k => ?_, fun k => ?_⟩
    · ext a b
      simp only [Matrix.sum_apply, hbord]
      exact hs3 a b
    · rw [psd_iff_fun]
      simp only [hbord]
      exact ⟨hs1 k, hs2 k⟩
    · simp only [mulVec_smul]
      exact smul_le_smul_of_nonneg_left (hπ k) (hα k)
  refine ⟨_, hfeas, fun s' hs' => ?_⟩
  have hobj : obj9 T h β x (V, v, v0, fun k => α k • π k) = g Ms := by
    simp only [obj9, hg, dotProduct_smul, smul_eq_mul, hπv]
    rfl
  rw [hobj]
  obtain ⟨hsum', hpsd', hdual'⟩ := hs'
  have hsumab : ∀ a b, ∑ k, bordered (s'.1 k) (s'.2.1 k) (s'.2.2.1 k) a b = Mb a b := by
    intro a b
    have := congrFun (congrFun hsum' a) b
    rw [Matrix.sum_apply] at this
    exact this
  set M' : Fin K → (Fin d ⊕ Fin 1) → (Fin d ⊕ Fin 1) → ℝ :=
    fun k a b => bordered (s'.1 k) (s'.2.1 k) (s'.2.2.1 k) a b with hM'
  have hM'F : M' ∈ Fs := by
    refine ⟨fun k a b => ((psd_iff_fun _).mp (hpsd' k)).1 a b,
      fun k y => ((psd_iff_fun _).mp (hpsd' k)).2 y, fun a b => ?_⟩
    exact hsumab a b
  have hle : obj9 T h β x s' ≤ g M' := by
    simp only [obj9, hg, hM']
    refine Finset.sum_le_sum fun k _ => ?_
    have := scaled_weak_duality W T h hA3 x hrec (α k) (hα k) (s'.2.1 k) (s'.2.2.2 k) (hdual' k)
    simp only [bordered, fromBlocks_apply₁₂, fromBlocks_apply₂₂, of_apply]
    linarith
  exact hle.trans (hmax hM'F)

end MSLP2Att

open MinimaxSLP.ObjExtremal in
theorem solution {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty) :
    ∃ s ∈ feasible9 W α μ Q, ∀ s' ∈ feasible9 W α μ Q, obj9 T h β x s' ≤ obj9 T h β x s :=
  MSLP2Att.att_main W T h α β hα μ Q hQ hA4 hA3 x hrec
