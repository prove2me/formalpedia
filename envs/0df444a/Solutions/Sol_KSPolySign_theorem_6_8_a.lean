-- Prove2me | solution 1 for KSPolySign.theorem_6_8_a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T14:28:48.300798+00:00
-- url     : https://prove2.me/submissions/f51a3381-b02d-4300-8e9d-46b8d8cff0f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
import Theorems.Thm_KSPolySign_lemma_3_1
import Theorems.Thm_KSPolySign_lemma_3_4
import Theorems.Thm_KSPolySign_lemma_3_7_a
import Theorems.Thm_KSPolySign_lemma_3_7_c
import Theorems.Thm_KSPolySign_lemma_3_10
import Theorems.Thm_KSPolySign_lemma_2_7
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecBalPoly_realOps
import Definitions.Def_KSPolySign_IsRatC
import Definitions.Def_KSPolySign_layout
open Matrix
open scoped ComplexOrder

namespace KSDescent

variable {k : ℕ}

local notation "E" => (Fin k → ℝ)

/-- curve -/
noncomputable def cv (y h s : E) (σ : ℝ) (t : ℝ) : E := y + (t ^ 2 / k) • h + (σ * t) • s
noncomputable def cvd (h s : E) (σ : ℝ) (t : ℝ) : E := (2 * t / k) • h + σ • s

theorem hasDerivAt_cv (y h s : E) (σ t : ℝ) : HasDerivAt (cv y h s σ) (cvd h s σ t) t := by
  unfold cv cvd
  have h1 : HasDerivAt (fun t : ℝ => (t ^ 2 / k) • h) ((2 * t / k) • h) t := by
    have := ((hasDerivAt_pow 2 t).div_const (k : ℝ)).smul_const h
    exact this.congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun t : ℝ => (σ * t) • s) (σ • s) t := by
    have := ((hasDerivAt_id t).const_mul σ).smul_const s
    simpa using this
  exact ((hasDerivAt_const t y).add h1).add h2 |>.congr_deriv (by simp)

theorem hasDerivAt_cvd (h s : E) (σ t : ℝ) : HasDerivAt (cvd h s σ) ((2 / k : ℝ) • h) t := by
  unfold cvd
  have := ((((hasDerivAt_id' t).const_mul 2).div_const (k : ℝ)).smul_const h).add_const (σ • s)
  exact this.congr_deriv (by norm_num)

theorem descent (f : E → ℝ) (O : Set E) (hO : IsOpen O) (y : E) (hy : y ∈ O)
    (hf : ContDiffOn ℝ 2 f O) (h : E) (K : Matrix (Fin k) (Fin k) ℝ) (hK : K.PosSemidef)
    (hneg : ∑ i, h i * fderiv ℝ f y (Pi.single i 1) +
      (1 / 2) * ∑ i, ∑ j, K i j * fderiv ℝ (fun x => fderiv ℝ f x (Pi.single j 1)) y (Pi.single i 1) < 0) :
    ∃ x ∈ O, f x < f y := by
  classical
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp at hneg
    · exact h0
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  set D1 := fderiv ℝ f with hD1
  have hfy : ContDiffAt ℝ 2 f y := hf.contDiffAt (hO.mem_nhds hy)
  have hdiffO : ∀ x ∈ O, HasFDerivAt f (D1 x) x := fun x hx =>
    ((hf.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hx)).hasFDerivAt
  have hD1y : DifferentiableAt ℝ D1 y :=
    (hfy.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set D2 := fderiv ℝ D1 y with hD2def
  have hD2 : HasFDerivAt D1 D2 y := hD1y.hasFDerivAt
  have hhess : ∀ v w : E, fderiv ℝ (fun x => D1 x v) y w = D2 w v := by
    intro v w
    have := hD2.clm_apply (hasFDerivAt_const v y)
    rw [this.fderiv]; simp
  -- decompose K
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin k) (Fin k) ℝ, ∀ i j, K i j = ∑ l, S l i * S l j := by
    open scoped MatrixOrder Matrix.Norms.L2Operator in
    obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hK.nonneg
    refine ⟨S, fun i j => ?_⟩
    rw [hS]
    simp [mul_apply, star_eq_conjTranspose, conjTranspose_apply]
  set s : Fin k → E := fun l i => S l i with hs
  have hs_sum : ∀ l, s l = ∑ i, S l i • (Pi.single i 1 : E) := by
    intro l; ext j; simp [s, Finset.sum_apply, Pi.single_apply]
  have hh_sum : h = ∑ i, h i • (Pi.single i 1 : E) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have hgrad : ∑ i, h i * D1 y (Pi.single i 1) = D1 y h := by
    conv_rhs => rw [hh_sum]
    simp [map_sum, map_smul]
  have hhs : ∑ i, ∑ j, K i j * fderiv ℝ (fun x => D1 x (Pi.single j 1)) y (Pi.single i 1)
      = ∑ l, D2 (s l) (s l) := by
    simp only [hhess]
    have : ∀ l, D2 (s l) (s l) = ∑ i, ∑ j, S l i * S l j * D2 (Pi.single i 1) (Pi.single j 1) := by
      intro l
      conv_lhs => rw [hs_sum l]
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [this, hS, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  set Q := D1 y h + (1 / 2) * ∑ l, D2 (s l) (s l) with hQdef
  have hQ : Q < 0 := by rw [hQdef, ← hgrad, ← hhs]; exact hneg
  -- curves
  have hcv0 : ∀ v : E, ∀ σ : ℝ, cv y h v σ 0 = y := by intro v σ; simp [cv]
  have hcvd0 : ∀ v : E, ∀ σ : ℝ, cvd h v σ 0 = σ • v := by intro v σ; simp [cvd]
  set G : ℝ → ℝ := fun t => ∑ l, (f (cv y h (s l) 1 t) + f (cv y h (s l) (-1) t)) with hG
  set g1 : ℝ → ℝ := fun t => ∑ l, (D1 (cv y h (s l) 1 t) (cvd h (s l) 1 t) +
      D1 (cv y h (s l) (-1) t) (cvd h (s l) (-1) t)) with hg1
  have hcont : ∀ v : E, ∀ σ : ℝ, Continuous (cv y h v σ) :=
    fun v σ => continuous_iff_continuousAt.mpr fun t => (hasDerivAt_cv y h v σ t).continuousAt
  have hev : ∀ᶠ t in nhds (0:ℝ), ∀ l, cv y h (s l) 1 t ∈ O ∧ cv y h (s l) (-1) t ∈ O := by
    rw [Filter.eventually_all]
    intro l
    have h1 := (hcont (s l) 1).continuousAt (x := 0) (hO.mem_nhds (by rw [hcv0]; exact hy))
    have h2 := (hcont (s l) (-1)).continuousAt (x := 0) (hO.mem_nhds (by rw [hcv0]; exact hy))
    exact Filter.inter_mem h1 h2
  have hGd : ∀ t, (∀ l, cv y h (s l) 1 t ∈ O ∧ cv y h (s l) (-1) t ∈ O) → HasDerivAt G (g1 t) t := by
    intro t ht
    apply HasDerivAt.fun_sum
    intro l _
    exact ((hdiffO _ (ht l).1).comp_hasDerivAt t (hasDerivAt_cv y h (s l) 1 t)).add
      ((hdiffO _ (ht l).2).comp_hasDerivAt t (hasDerivAt_cv y h (s l) (-1) t))
  have hterm : ∀ v : E, ∀ σ : ℝ, HasDerivAt (fun t => D1 (cv y h v σ t) (cvd h v σ t))
      (D1 y ((2 / k : ℝ) • h) + D2 (σ • v) (σ • v)) 0 := by
    intro v σ
    have hc : HasDerivAt (fun t => D1 (cv y h v σ t)) (D2 (cvd h v σ 0)) 0 := by
      have hD2' : HasFDerivAt D1 D2 (cv y h v σ 0) := by rw [hcv0]; exact hD2
      exact hD2'.comp_hasDerivAt 0 (hasDerivAt_cv y h v σ 0)
    have := hc.clm_apply (hasDerivAt_cvd h v σ 0)
    rw [hcv0, hcvd0] at this
    simpa [add_comm] using this
  have hg1d : HasDerivAt g1 (4 * Q) 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (x := (0:ℝ)) (fun l _ => (hterm (s l) 1).add (hterm (s l) (-1)))
    refine this.congr_deriv ?_
    simp only [one_smul, neg_smul, map_neg, ContinuousLinearMap.neg_apply, neg_neg, map_smul,
      smul_eq_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hQdef]
    field_simp
    ring
  have hg10 : g1 0 = 0 := by
    simp only [hg1, hcv0, hcvd0, one_smul, neg_smul, map_neg, add_neg_cancel, Finset.sum_const_zero]
  -- g1 < 0 to the right of 0
  have hneg_right : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), g1 t < 0 := by
    have hT := hg1d.tendsto_slope_zero_right
    have hlt : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t⁻¹ • (g1 (0 + t) - g1 0) < 0 :=
      hT (Iio_mem_nhds (by linarith))
    filter_upwards [hlt, self_mem_nhdsWithin] with t ht htpos
    rw [hg10, zero_add, sub_zero, smul_eq_mul] at ht
    have htp : 0 < t := htpos
    by_contra hc
    push_neg at hc
    have : 0 ≤ t⁻¹ * g1 t := mul_nonneg (inv_nonneg.mpr htp.le) hc
    linarith
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨ε', hε', hε'sub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hneg_right
  set t := min ε ε' / 2 with ht_def
  have htpos : 0 < t := half_pos (lt_min hε hε')
  have htε : t < ε := by have := min_le_left ε ε'; linarith
  have htε' : t < ε' := by have := min_le_right ε ε'; linarith
  have hin : ∀ x ∈ Set.Icc (0:ℝ) t, ∀ l, cv y h (s l) 1 x ∈ O ∧ cv y h (s l) (-1) x ∈ O := by
    intro x hx
    apply hεball
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]; linarith [hx.2]
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope G g1 htpos
    (fun x hx => (hGd x (hin x hx)).continuousAt.continuousWithinAt)
    (fun x hx => hGd x (hin x (Set.Ioo_subset_Icc_self hx)))
  have hgc : g1 c < 0 := hε'sub ⟨hc.1, by linarith [hc.2]⟩
  have hGlt : G t < G 0 := by
    rw [hcslope, sub_zero] at hgc
    have := (div_neg_iff.mp hgc)
    rcases this with h1 | h1
    · linarith [h1.2]
    · linarith [h1.1]
  have hG0 : G 0 = ∑ _l : Fin k, (f y + f y) := by simp only [hG, hcv0]
  rw [hG0] at hGlt
  obtain ⟨l, _, hl⟩ := Finset.exists_lt_of_sum_lt hGlt
  have hmem := hin t ⟨htpos.le, le_rfl⟩ l
  by_cases h1 : f (cv y h (s l) 1 t) < f y
  · exact ⟨_, hmem.1, h1⟩
  · exact ⟨_, hmem.2, by push_neg at h1; linarith⟩

end KSDescent


namespace KSPolySign.Exist
open KSPolySign

theorem faceProj_self {k : ℕ} (y : Fin k → ℝ) : faceProj y y = y := by
  funext i; simp [faceProj]

theorem vertex (n k : ℕ) (hn : 1 ≤ n) (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (hC : IsInstance C)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ y : Fin k → ℝ, (∀ i, y i = 1 ∨ y i = -1) ∧ pot C 0 ρ y ≤ pot C 0 ρ 0 := by
  classical
  have hF0 : (0 : Matrix (Fin n) (Fin n) ℂ).IsHermitian := isHermitian_zero
  set Q : Set (Fin k → ℝ) := {x | ∀ i, |x i| ≤ 1} with hQ
  have hQc : IsCompact Q := by
    have : Q = Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1) := by
      ext x; simp only [hQ, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]
    rw [this]; exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have h0Q : (0 : Fin k → ℝ) ∈ Q := by simp [hQ]
  have hcont := (lemma_3_7_c n k hn C hC 0 hF0 ρ hρ).1
  obtain ⟨y0, hy0Q, hmin0⟩ := hQc.exists_isMinOn ⟨0, h0Q⟩ hcont
  let act : (Fin k → ℝ) → ℕ := fun x => (Finset.univ.filter (fun i => |x i| < 1)).card
  have hex : ∃ j, ∃ x ∈ Q, pot C 0 ρ x ≤ pot C 0 ρ y0 ∧ act x = j := ⟨_, y0, hy0Q, le_rfl, rfl⟩
  obtain ⟨y, hyQ, hyP, hyact⟩ := Nat.find_spec hex
  have hyMin : ∀ z ∈ Q, pot C 0 ρ y ≤ pot C 0 ρ z := fun z hz => hyP.trans (hmin0 hz)
  have hnoact : ∀ i, ¬ |y i| < 1 := by
    intro i0 hi0
    obtain ⟨b, U, V, hopt, -⟩ := lemma_3_7_a n k hn C hC 0 hF0 ρ hρ y hyQ
    by_cases hl : ∀ i, |y i| < 1 →
        iota * beta (y i) * (C i * U).trace.re < 1 + y i ∧
        iota * beta (y i) * (C i * V).trace.re < 1 - y i
    · have hlight : IsLight C 0 ρ y := ⟨hyQ, b, U, V, hopt, hl⟩
      obtain ⟨h, K, hK, -, hneg⟩ := lemma_2_7 n k hn C hC 0 hF0 ρ hρ y hlight ⟨i0, hi0⟩
      obtain ⟨bf, Uf, Vf, Wf, Zf, -, ⟨hC2, -⟩, -⟩ := (lemma_3_7_c n k hn C hC 0 hF0 ρ hρ).2 y hyQ
      set O : Set (Fin k → ℝ) := {x | ∀ i, |y i| < 1 → |x i| < 1} with hO
      have hOopen : IsOpen O := by
        rw [hO, Set.setOf_forall]
        refine isOpen_iInter_of_finite fun i => ?_
        by_cases hyi : |y i| < 1
        · simp only [hyi, true_implies]
          exact isOpen_lt ((continuous_apply i).abs) continuous_const
        · simp [hyi]
      have hyO : y ∈ O := fun i hi => hi
      obtain ⟨x, hxO, hxlt⟩ := KSDescent.descent (faceFun C 0 ρ y) O hOopen y hyO hC2 h K hK hneg
      have hxQ : faceProj y x ∈ Q := by
        intro i
        simp only [faceProj]
        split_ifs with hyi
        · exact (hxO i hyi).le
        · exact hyQ i
      have := hyMin _ hxQ
      simp only [faceFun, faceProj_self] at hxlt
      linarith
    · push_neg at hl
      obtain ⟨i, hi, hcond⟩ := hl
      have h310 := lemma_3_10 n k hn C hC 0 hF0 ρ hρ y hyQ b U V hopt i hi
      obtain ⟨s, hs, hpot⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
          pot C 0 ρ (Function.update y i s) ≤ pot C 0 ρ y := by
        by_cases hu : iota * beta (y i) * (C i * U).trace.re < 1 + y i
        · exact ⟨1, Or.inl rfl, (h310.1 (hcond hu)).2⟩
        · push_neg at hu
          exact ⟨-1, Or.inr rfl, (h310.2 hu).2⟩
      set y' := Function.update y i s
      have hy'Q : y' ∈ Q := by
        intro j
        by_cases hj : j = i
        · subst hj; simp only [y', Function.update_self]; rcases hs with h | h <;> simp [h]
        · simp only [y', Function.update_of_ne hj]; exact hyQ j
      have hact : act y' < act y := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i, by simp [hi], ?_⟩
          simp only [y', Finset.mem_filter, Function.update_self, Finset.mem_univ, true_and]
          rcases hs with h | h <;> simp [h]
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          by_cases hji : j = i
          · subst hji; simp only [y', Function.update_self] at hj; rcases hs with h | h <;> simp [h] at hj
          · simpa [y', Function.update_of_ne hji] using hj
      have := Nat.find_min hex (hyact ▸ hact)
      exact this ⟨y', hy'Q, hpot.trans hyP, rfl⟩
  refine ⟨y, fun i => ?_, hyMin 0 h0Q⟩
  have h1 := hyQ i
  have h2 := hnoact i
  have : |y i| = 1 := le_antisymm h1 (not_lt.mp h2)
  rcases abs_eq (zero_le_one) |>.mp this with h | h
  · exact Or.inl h
  · exact Or.inr h


section L2
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem opNorm_eq_l2 {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    AgnosticTNS.opNorm M = ‖M‖ := by
  rw [Matrix.cstar_norm_def, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
  unfold AgnosticTNS.opNorm
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.toLp 2 x, ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq]; exact Real.sqrt_le_one.mpr hx
    · rw [EuclideanSpace.norm_eq]; simp
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.ofLp, ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq] at hx
      simpa using (Real.sqrt_le_one (x := ∑ i, ‖x i‖ ^ 2)).mp hx
    · rw [EuclideanSpace.norm_eq]; simp

theorem algebraMap_eq {n : ℕ} (r : ℝ) :
    algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) r = ((r : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one]
  ext i j
  simp [Matrix.smul_apply, one_apply]

theorem herm_le_norm {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) :
    (((‖X‖ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef := by
  have hsa : IsSelfAdjoint X := hX
  have := hsa.le_algebraMap_norm_self
  rw [algebraMap_eq] at this
  exact Matrix.le_iff.mp this

theorem eq_zero_of_rank_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : A.rank = 0) : A = 0 := by
  have h1 : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
  have h2 : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp h1
  ext i j
  have := congrFun (LinearMap.congr_fun h2 (Pi.single j 1)) i
  simpa [mulVec_single] using this

theorem exist_main :
    (∀ (m n : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ i, (A i).IsHermitian ∧ (A i).rank ≤ 1) →
      ∃ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        AgnosticTNS.opNorm (∑ i, ((σ i : ℝ) : ℂ) • A i) ≤
          3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, A i * A i))) := by
  classical
  intro m n A hA
  set s := Finset.univ.filter (fun i => A i ≠ 0) with hs_def
  set m' := s.card
  let e : Fin m' ≃ s := s.equivFin.symm
  set B : Fin m' → Matrix (Fin n) (Fin n) ℂ := fun j => A (e j) with hB_def
  have htrans : ∀ F : Fin m → Matrix (Fin n) (Fin n) ℂ, (∀ i, A i = 0 → F i = 0) →
      ∑ i, F i = ∑ j, F (e j) := by
    intro F hF
    rw [← Finset.sum_filter_of_ne (p := fun i => A i ≠ 0) (fun i _ hFi hAi => hFi (hF i hAi))]
    rw [← Finset.sum_coe_sort]
    exact (Equiv.sum_comp e (fun x : s => F x)).symm
  have hB : ∀ j, (B j).IsHermitian ∧ (B j).rank = 1 := by
    intro j
    refine ⟨(hA _).1, ?_⟩
    have hne : A (e j) ≠ 0 := (Finset.mem_filter.mp (e j).2).2
    have := (hA (e j)).2
    rcases Nat.lt_or_ge (A (e j)).rank 1 with h | h
    · exact absurd (eq_zero_of_rank_eq_zero _ (by omega)) hne
    · exact le_antisymm this h
  have hsumAA : ∑ i, A i * A i = ∑ j, B j * B j := htrans (fun i => A i * A i) (fun i h => by simp [h])
  rcases Nat.eq_zero_or_pos m' with hm0 | hm'
  · -- all zero
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    have : ∑ i, (((1 : ℝ) : ℝ) : ℂ) • A i = 0 := by
      rw [htrans _ (fun i h => by simp [h])]
      have : IsEmpty (Fin m') := by rw [hm0]; exact Fin.isEmpty'
      simp
    rw [this, opNorm_eq_l2, norm_zero]
    positivity
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hr := (hB ⟨0, hm'⟩).2
      have hle := Matrix.rank_le_card_width (B ⟨0, hm'⟩)
      rw [hr, Fintype.card_fin, h] at hle
      omega
    · exact h
  obtain ⟨⟨hPSD, -, hζlow, hζ1, -⟩, htau, hvar⟩ := lemma_3_1 m' n hm' B hB
  set L : ℝ := ∑ i, |(B i).trace.re| with hL
  set ε : Fin m' → ℝ := fun i => if 0 < (B i).trace.re then 1 else -1 with hε
  set Bbar : Fin m' → Matrix (Fin n) (Fin n) ℂ := fun i => ((ε i / L : ℝ) : ℂ) • B i with hBbar
  set ζ : ℝ := AgnosticTNS.opNorm (∑ i, Bbar i * Bbar i) with hζ
  have hζpos : 0 < ζ := lt_of_lt_of_le (by positivity) hζlow
  have hinst : IsInstance Bbar := by
    refine ⟨hPSD, ?_⟩
    have hH : (∑ i, Bbar i * Bbar i).IsHermitian := by
      unfold IsHermitian
      rw [conjTranspose_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [conjTranspose_mul, (hPSD i).1.isHermitian.eq]
    have := (herm_le_norm hH).add (PosSemidef.one.smul (a := (((1 - ζ) : ℝ) : ℂ))
      (by exact_mod_cast sub_nonneg.mpr hζ1))
    rw [← opNorm_eq_l2] at this
    convert this using 1
    rw [← hζ]; push_cast; rw [sub_smul, one_smul]; abel
  set ρ : ℝ := ((3.4814 : ℝ) ^ 2 / 4 - 3.03) * ζ / (2 * n) with hρ
  have hρpos : 0 < ρ := by
    have : (0:ℝ) < (3.4814 : ℝ) ^ 2 / 4 - 3.03 := by norm_num
    positivity
  obtain ⟨τ, hτ, hpot⟩ := vertex n m' hn Bbar hinst ρ hρpos
  have h34 := lemma_3_4
  have hb1 := ((h34.2 n m' hn Bbar hinst ρ hρpos).1 0 isHermitian_zero τ
    (fun i => by rcases hτ i with h | h <;> simp [h])).2
  have hb2 := (h34.2 n m' hn Bbar hinst ρ hρpos).2 ζ le_rfl
  have hMs : Msum Bbar 0 τ = ∑ i, ((τ i : ℝ) : ℂ) • Bbar i := by simp [Msum]
  rw [hMs] at hb1
  have hS : iota * ζ + 2 * n * ρ = ((3.4814 : ℝ) / 2) ^ 2 * ζ := by
    rw [hρ]; have : (n : ℝ) ≠ 0 := by positivity
    field_simp; norm_num [iota]
  have hbound : AgnosticTNS.opNorm (∑ i, ((τ i : ℝ) : ℂ) • Bbar i) ≤ 3.4814 * Real.sqrt ζ := by
    refine hb1.trans (hpot.trans (hb2.trans (le_of_eq ?_)))
    rw [hS, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]; ring
  -- signs
  let σ : Fin m → ℝ := fun i => if hi : i ∈ s then ε (e.symm ⟨i, hi⟩) * τ (e.symm ⟨i, hi⟩) else 1
  have hσe : ∀ j, σ (e j) = ε j * τ j := by
    intro j; simp only [σ]; rw [dif_pos (e j).2]; simp
  refine ⟨σ, fun i => ?_, ?_⟩
  · simp only [σ]
    split_ifs
    · have h1 : ε (e.symm ⟨i, by assumption⟩) = 1 ∨ ε (e.symm ⟨i, by assumption⟩) = -1 := by
        simp only [hε]; split_ifs <;> simp
      rcases h1 with h1 | h1 <;> rcases hτ (e.symm ⟨i, by assumption⟩) with h2 | h2 <;>
        simp [h1, h2]
    · exact Or.inl rfl
  · rw [htrans (fun i => ((σ i : ℝ) : ℂ) • A i) (fun i h => by simp [h])]
    simp only [hσe]
    have := htau τ hτ
    rw [show (∑ j, ((ε j * τ j : ℝ) : ℂ) • A (e j)) = ∑ j, ((ε j * τ j : ℝ) : ℂ) • B j from rfl, this,
      hsumAA, hvar]
    have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hL0]
    calc L * AgnosticTNS.opNorm (∑ i, ((τ i : ℝ) : ℂ) • Bbar i) ≤ L * (3.4814 * Real.sqrt ζ) :=
          mul_le_mul_of_nonneg_left hbound hL0
      _ = 3.4814 * (L * Real.sqrt ζ) := by ring

end L2

end KSPolySign.Exist

open KSPolySign

theorem solution :
    (∀ (m n : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ i, (A i).IsHermitian ∧ (A i).rank ≤ 1) →
      ∃ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        AgnosticTNS.opNorm (∑ i, ((σ i : ℝ) : ℂ) • A i) ≤
          3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, A i * A i))) :=
  KSPolySign.Exist.exist_main
