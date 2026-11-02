-- Prove2me | solution 1 for LatticeHamSim.StrictLR.eq_44
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:51:52.086084+00:00
-- url     : https://prove2.me/submissions/4c6e1066-c6f4-485b-a4e8-f7bdb995dead

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
import Theorems.Thm_LatticeHamSim_StrictLR_eq_28
import Theorems.Thm_LatticeHamSim_StrictLR_eq_42
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Aux_LHS_44

open LatticeHamSim.CommLR LatticeHamSim.StrictLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}

noncomputable local instance : NormedAlgebra ℚ (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

lemma comm_bound (P B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖P * B - B * P‖ ≤ 2 * ‖P‖ * ‖B‖ := by
  calc ‖P * B - B * P‖ ≤ ‖P * B‖ + ‖B * P‖ := norm_sub_le _ _
    _ ≤ ‖P‖ * ‖B‖ + ‖B‖ * ‖P‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖P‖ * ‖B‖ := by ring

lemma evolve_norm (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (t : ℝ) (O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖evolve (H h) t O‖ = ‖O‖ := by
  have hsa : star (H h) = H h := by
    unfold H
    rw [star_sum]
    exact Finset.sum_congr rfl (fun X _ => hherm X)
  have key : ∀ s : ℝ, NormedSpace.exp ((Complex.I * (s : ℂ)) • H h) ∈
      unitary (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
    intro s
    have hs : ((s : ℂ) • H h) ∈ selfAdjoint (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
      rw [selfAdjoint.mem_iff, star_smul, hsa, Complex.star_def, Complex.conj_ofReal]
    have := (selfAdjoint.expUnitary ⟨(s : ℂ) • H h, hs⟩).prop
    simp only [selfAdjoint.expUnitary_coe, smul_smul] at this
    exact this
  unfold evolve
  have hU := key t
  have hV := key (-t)
  rw [show (-(Complex.I * (t : ℂ))) = Complex.I * ((-t : ℝ) : ℂ) by push_cast; ring]
  rw [CStarRing.norm_mul_mem_unitary _ hV, CStarRing.norm_mem_unitary_mul _ hU]

lemma cb_bddAbove (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    BddAbove {r : ℝ | ∃ A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
      SupportedOn X A ∧ ‖A‖ ≤ 1 ∧
      r = ‖evolve (H h) t A * B - B * evolve (H h) t A‖} := by
  refine ⟨2 * ‖B‖, ?_⟩
  rintro r ⟨A, -, hA1, rfl⟩
  refine le_trans (comm_bound _ _) ?_
  rw [evolve_norm h hherm]
  nlinarith [norm_nonneg A, norm_nonneg B]

lemma cb_set_nonempty (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    {r : ℝ | ∃ A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
      SupportedOn X A ∧ ‖A‖ ≤ 1 ∧
      r = ‖evolve (H h) t A * B - B * evolve (H h) t A‖}.Nonempty := by
  refine ⟨0, 0, ⟨0, fun σ τ => by simp⟩, by simp, ?_⟩
  simp [evolve]

lemma continuous_exp_line (J : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (c : ℂ) :
    Continuous (fun s : ℝ => NormedSpace.exp ((c * (s : ℂ)) • J)) := by
  exact NormedSpace.exp_continuous.comp ((continuous_const.mul Complex.continuous_ofReal).smul continuous_const)

lemma cb_sub_le (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) (s₁ s₂ : ℝ) :
    CB h B Z s₁ - CB h B Z s₂ ≤
      2 * ‖B‖ * (‖NormedSpace.exp ((Complex.I * (s₁ : ℂ)) • H h) -
          NormedSpace.exp ((Complex.I * (s₂ : ℂ)) • H h)‖ *
        ‖NormedSpace.exp ((-(Complex.I * (s₁ : ℂ))) • H h)‖ +
        ‖NormedSpace.exp ((Complex.I * (s₂ : ℂ)) • H h)‖ *
        ‖NormedSpace.exp ((-(Complex.I * (s₁ : ℂ))) • H h) -
          NormedSpace.exp ((-(Complex.I * (s₂ : ℂ))) • H h)‖) := by
  set U : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((Complex.I * (s : ℂ)) • H h)
  set V : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • H h)
  set M : ℝ := 2 * ‖B‖ * (‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖)
  rw [sub_le_iff_le_add]
  unfold CB
  refine csSup_le (cb_set_nonempty h B Z s₁) ?_
  rintro r ⟨A, hAsupp, hA1, rfl⟩
  have hmem2 : ‖evolve (H h) s₂ A * B - B * evolve (H h) s₂ A‖ ≤ CB h B Z s₂ := by
    refine le_csSup (cb_bddAbove h hherm B Z s₂) ⟨A, hAsupp, hA1, rfl⟩
  have hdiff : evolve (H h) s₁ A - evolve (H h) s₂ A =
      (U s₁ - U s₂) * A * V s₁ + U s₂ * A * (V s₁ - V s₂) := by
    unfold evolve U V
    noncomm_ring
  have hev_diff : ‖evolve (H h) s₁ A - evolve (H h) s₂ A‖ ≤
      ‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖ := by
    rw [hdiff]
    calc ‖(U s₁ - U s₂) * A * V s₁ + U s₂ * A * (V s₁ - V s₂)‖
        ≤ ‖(U s₁ - U s₂) * A * V s₁‖ + ‖U s₂ * A * (V s₁ - V s₂)‖ := norm_add_le _ _
      _ ≤ ‖(U s₁ - U s₂) * A‖ * ‖V s₁‖ + ‖U s₂ * A‖ * ‖V s₁ - V s₂‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (‖U s₁ - U s₂‖ * ‖A‖) * ‖V s₁‖ + (‖U s₂‖ * ‖A‖) * ‖V s₁ - V s₂‖ :=
          add_le_add (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖U s₁ - U s₂‖ * 1) * ‖V s₁‖ + (‖U s₂‖ * 1) * ‖V s₁ - V s₂‖ := by
          gcongr
      _ = ‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖ := by ring
  have hcomm_diff : ‖(evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
      (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A)‖ ≤ M := by
    have heq : (evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
        (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A) =
        (evolve (H h) s₁ A - evolve (H h) s₂ A) * B - B * (evolve (H h) s₁ A - evolve (H h) s₂ A) := by
      noncomm_ring
    rw [heq]
    calc ‖(evolve (H h) s₁ A - evolve (H h) s₂ A) * B - B * (evolve (H h) s₁ A - evolve (H h) s₂ A)‖
        ≤ 2 * ‖evolve (H h) s₁ A - evolve (H h) s₂ A‖ * ‖B‖ := comm_bound _ _
      _ ≤ 2 * (‖U s₁ - U s₂‖ * ‖V s₁‖ + ‖U s₂‖ * ‖V s₁ - V s₂‖) * ‖B‖ := by
          gcongr
      _ = M := by unfold M; ring
  calc ‖evolve (H h) s₁ A * B - B * evolve (H h) s₁ A‖
      ≤ ‖evolve (H h) s₂ A * B - B * evolve (H h) s₂ A‖ +
        ‖(evolve (H h) s₁ A * B - B * evolve (H h) s₁ A) -
          (evolve (H h) s₂ A * B - B * evolve (H h) s₂ A)‖ := norm_le_insert' _ _
    _ ≤ CB h B Z s₂ + M := add_le_add hmem2 hcomm_diff
    _ = M + CB h B Z s₂ := add_comm _ _

lemma continuous_CB (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Z : Finset Λ) :
    Continuous (fun s : ℝ => CB h B Z s) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set U : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((Complex.I * (s : ℂ)) • H h)
  set V : ℝ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
    fun s => NormedSpace.exp ((-(Complex.I * (s : ℂ))) • H h)
  have hU : Continuous U := continuous_exp_line (H h) Complex.I
  have hV : Continuous V := by
    have : V = fun s : ℝ => NormedSpace.exp (((-Complex.I) * (s : ℂ)) • H h) := by
      ext s; unfold V; rw [neg_mul]
    rw [this]
    exact continuous_exp_line (H h) (-Complex.I)
  set F : ℝ → ℝ := fun s =>
    max (2 * ‖B‖ * (‖U s - U s₀‖ * ‖V s‖ + ‖U s₀‖ * ‖V s - V s₀‖))
        (2 * ‖B‖ * (‖U s₀ - U s‖ * ‖V s₀‖ + ‖U s‖ * ‖V s₀ - V s‖))
  have hF_cont : Continuous F := by
    unfold F
    refine Continuous.max ?_ ?_
    · exact continuous_const.mul (((hU.sub continuous_const).norm.mul hV.norm).add
        (continuous_const.mul (hV.sub continuous_const).norm))
    · exact continuous_const.mul (((continuous_const.sub hU).norm.mul continuous_const).add
        (hU.norm.mul (continuous_const.sub hV).norm))
  have hF0 : F s₀ = 0 := by
    unfold F
    simp
  have hFtend : Filter.Tendsto F (nhds s₀) (nhds 0) := by
    rw [← hF0]
    exact hF_cont.continuousAt
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hFtend
  rw [Real.norm_eq_abs, abs_le]
  have h1 : CB h B Z s₀ - CB h B Z s ≤ F s :=
    (cb_sub_le h hherm B Z s₀ s).trans (le_max_right _ _)
  have h2 : CB h B Z s - CB h B Z s₀ ≤ F s :=
    (cb_sub_le h hherm B Z s s₀).trans (le_max_left _ _)
  constructor <;> linarith

lemma linked_cons_iff {k : ℕ} (P Q : Finset Λ) (Z' : Fin k → Finset Λ) :
    Linked P (Fin.cons Q Z') ↔ meets P Q ∧ Linked Q Z' := by
  unfold Linked
  rw [Fin.forall_fin_succ]
  apply and_congr
  · rfl
  · refine forall_congr' (fun j => ?_)
    have hch : chain P (Fin.cons Q Z') j.succ.castSucc = chain Q Z' j.castSucc := by
      unfold chain
      rw [Fin.castSucc_succ, Fin.cons_succ]
    rw [hch, Fin.cons_succ]

lemma linkedSum_succ (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (P : Finset Λ) (k : ℕ) :
    linkedSum h P (k + 1) =
      ∑ Q ∈ Finset.univ.filter (fun Q => meets P Q), ‖h Q‖ * linkedSum h Q k := by
  unfold linkedSum
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => Finset Λ)), Fintype.sum_prod_type]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  split_ifs with hPQ
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Z' _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [Fin.consEquiv_apply, Prod.fst, Prod.snd, Fin.cons_zero, Fin.cons_succ]
    have hiff := linked_cons_iff P Q Z'
    split_ifs with h1 h2 h2
    · ring
    · exfalso; exact h2 (hiff.mp h1).2
    · exfalso; exact h1 (hiff.mpr ⟨hPQ, h2⟩)
    · ring
  · refine Finset.sum_eq_zero (fun Z' _ => ?_)
    simp only [Fin.consEquiv_apply, Prod.fst, Prod.snd]
    have hiff := linked_cons_iff P Q Z'
    split_ifs with h1
    · exfalso; exact hPQ (hiff.mp h1).1
    · ring

lemma linkedSum_zero (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (P : Finset Λ) :
    linkedSum h P 0 = 1 := by
  unfold linkedSum
  rw [Finset.univ_unique, Finset.sum_singleton]
  have hL : ∀ f : Fin 0 → Finset Λ, Linked P f := fun _ j => Fin.elim0 j
  split_ifs with h1
  · simp
  · exfalso; exact h1 (hL _)

lemma linkedSum_nonneg (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (P : Finset Λ) (k : ℕ) :
    0 ≤ linkedSum h P k := by
  classical
  unfold linkedSum
  refine Finset.sum_nonneg (fun Z _ => ?_)
  refine mul_nonneg (Finset.prod_nonneg (fun j _ => norm_nonneg _)) ?_
  split_ifs <;> positivity

lemma eq_44_iter (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, SupportedOn X (h X))
    (hloc : ∀ X : Finset Λ, 1 < Metric.diam (X : Set Λ) → h X = 0)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Y : Finset Λ) (hB : SupportedOn Y B) :
    ∀ (k : ℕ) (X : Finset Λ),
      (∀ x ∈ X, ∀ y ∈ Y, (k : ℝ) ≤ dist x y) →
      ∀ (t : ℝ), 0 ≤ t →
      CB h B X t ≤ 2 * ‖B‖ * (2 * t) ^ k / (k.factorial : ℝ) * linkedSum h X k
  | 0, X, _, t, _ => by
    rw [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one, linkedSum_zero, mul_one]
    exact (eq_28 h hherm hsupp B Y hB X t).2.1
  | k + 1, X, hdist, t, ht => by
    have hnotmeets : ¬ meets X Y := by
      rintro ⟨x, hx⟩
      have hxX := (Finset.mem_inter.mp hx).1
      have hxY := (Finset.mem_inter.mp hx).2
      have := hdist x hxX x hxY
      rw [dist_self] at this
      have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hCB0 : CB h B X 0 ≤ 0 := by
      have h0 := (eq_28 h hherm hsupp B Y hB X 0).1
      simpa [hnotmeets] using h0
    have h42 := eq_42 h hherm hsupp B X t ht
    have hsum_bound :
        ∑ Z ∈ Finset.univ.filter (fun Z => meets X Z),
          ‖h Z‖ * ∫ s in (0 : ℝ)..t, CB h B Z s ≤
        ∑ Z ∈ Finset.univ.filter (fun Z => meets X Z),
          ‖h Z‖ * (2 * ‖B‖ * (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) / 2 * linkedSum h Z k) := by
      refine Finset.sum_le_sum (fun Z hZ => ?_)
      by_cases hz : h Z = 0
      · simp [hz]
      · have hdiam : Metric.diam (Z : Set Λ) ≤ 1 := by
          by_contra hc
          exact hz (hloc Z (not_le.mp hc))
        have hXZ : (X ∩ Z).Nonempty := (Finset.mem_filter.mp hZ).2
        obtain ⟨x₀, hx₀⟩ := hXZ
        have hx₀X := (Finset.mem_inter.mp hx₀).1
        have hx₀Z := (Finset.mem_inter.mp hx₀).2
        have hdistZ : ∀ z ∈ Z, ∀ y ∈ Y, (k : ℝ) ≤ dist z y := by
          intro z hzZ y hyY
          have h1 : dist x₀ z ≤ 1 :=
            (Metric.dist_le_diam_of_mem (Z.finite_toSet.isBounded) hx₀Z hzZ).trans hdiam
          have h2 : ((k + 1 : ℕ) : ℝ) ≤ dist x₀ y := hdist x₀ hx₀X y hyY
          have h3 : dist x₀ y ≤ dist x₀ z + dist z y := dist_triangle x₀ z y
          push_cast at h2
          linarith
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        set C : ℝ := 2 * ‖B‖ * 2 ^ k / (k.factorial : ℝ) * linkedSum h Z k
        have hint_le : ∫ s in (0 : ℝ)..t, CB h B Z s ≤ ∫ s in (0 : ℝ)..t, C * s ^ k := by
          refine intervalIntegral.integral_mono_on ht
            ((continuous_CB h hherm B Z).intervalIntegrable 0 t)
            ((continuous_const.mul (continuous_pow k)).intervalIntegrable 0 t)
            (fun s hs => ?_)
          have hih := eq_44_iter h hherm hsupp hloc B Y hB k Z hdistZ s hs.1
          have heq : 2 * ‖B‖ * (2 * s) ^ k / (k.factorial : ℝ) * linkedSum h Z k = C * s ^ k := by
            unfold C
            rw [mul_pow]
            ring
          linarith
        have hint_eval : ∫ s in (0 : ℝ)..t, C * s ^ k =
            2 * ‖B‖ * (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) / 2 * linkedSum h Z k := by
          rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
          unfold C
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow, pow_succ]
          field_simp
          ring
        exact hint_le.trans (le_of_eq hint_eval)
    calc CB h B X t
        ≤ CB h B X 0 + 2 * ∑ Z ∈ Finset.univ.filter (fun Z => meets X Z),
            ‖h Z‖ * ∫ s in (0 : ℝ)..t, CB h B Z s := h42
      _ ≤ 0 + 2 * ∑ Z ∈ Finset.univ.filter (fun Z => meets X Z),
            ‖h Z‖ * (2 * ‖B‖ * (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) / 2 * linkedSum h Z k) :=
          add_le_add hCB0 (mul_le_mul_of_nonneg_left hsum_bound (by positivity))
      _ = 2 * ‖B‖ * (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) *
            ∑ Z ∈ Finset.univ.filter (fun Z => meets X Z), ‖h Z‖ * linkedSum h Z k := by
          rw [zero_add, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun Z _ => ?_)
          ring
      _ = 2 * ‖B‖ * (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * linkedSum h X (k + 1) := by
          rw [linkedSum_succ]

lemma setDist_nonneg (X Y : Finset Λ) : 0 ≤ setDist X Y := by
  unfold setDist
  split_ifs with hne
  · obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_inf' hne (fun p => dist p.1 p.2)
    rw [hpeq]
    exact dist_nonneg
  · exact le_rfl

lemma floor_setDist_le_dist (X Y : Finset Λ) (x : Λ) (hx : x ∈ X) (y : Λ) (hy : y ∈ Y) :
    (⌊setDist X Y⌋₊ : ℝ) ≤ dist x y := by
  refine (Nat.floor_le (setDist_nonneg X Y)).trans ?_
  unfold setDist
  have hmem : (x, y) ∈ X ×ˢ Y := Finset.mem_product.mpr ⟨hx, hy⟩
  have hne : (X ×ˢ Y).Nonempty := ⟨(x, y), hmem⟩
  rw [dif_pos hne]
  exact Finset.inf'_le (fun p => dist p.1 p.2) hmem

lemma cb_neg_time (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    CB h B X t = CB (fun Z => - h Z) B X (-t) := by
  have hH : H (fun Z => - h Z) = - H h := by
    unfold H
    rw [Finset.sum_neg_distrib]
  have hev : ∀ A, evolve (H (fun Z => - h Z)) (-t) A = evolve (H h) t A := by
    intro A
    unfold evolve
    simp only [hH, Complex.ofReal_neg, mul_neg, neg_neg, smul_neg, neg_smul]
  unfold CB
  simp only [hev]

lemma linkedSum_neg (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (X : Finset Λ) (k : ℕ) :
    linkedSum (fun Z => - h Z) X k = linkedSum h X k := by
  unfold linkedSum
  simp only [norm_neg]

end Aux_LHS_44

open LatticeHamSim.CommLR LatticeHamSim.StrictLR Aux_LHS_44 in
theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, LatticeHamSim.CommLR.SupportedOn X (h X))
    (hloc : ∀ X : Finset Λ, 1 < Metric.diam (X : Set Λ) → h X = 0)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X Y : Finset Λ) (hB : LatticeHamSim.CommLR.SupportedOn Y B) (t : ℝ) :
    LatticeHamSim.CommLR.CB h B X t ≤ 2 * ‖B‖ * (2 * |t|) ^ ⌊LatticeHamSim.CommLR.setDist X Y⌋₊ / (⌊LatticeHamSim.CommLR.setDist X Y⌋₊).factorial *
      linkedSum h X ⌊LatticeHamSim.CommLR.setDist X Y⌋₊ := by
  have hdist : ∀ x ∈ X, ∀ y ∈ Y, (⌊setDist X Y⌋₊ : ℝ) ≤ dist x y :=
    fun x hx y hy => floor_setDist_le_dist X Y x hx y hy
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    exact eq_44_iter h hherm hsupp hloc B Y hB ⌊setDist X Y⌋₊ X hdist t ht
  · have hnt : 0 ≤ -t := by linarith
    have habs : |t| = -t := abs_of_neg (not_le.mp ht)
    rw [habs, cb_neg_time h B X t, ← linkedSum_neg h X ⌊setDist X Y⌋₊]
    have hherm' : ∀ Z, (- h Z).IsHermitian := fun Z => (hherm Z).neg
    have hsupp' : ∀ Z, SupportedOn Z (- h Z) := by
      intro Z
      obtain ⟨m, hm⟩ := hsupp Z
      refine ⟨-m, fun σ τ => ?_⟩
      simp only [Matrix.neg_apply, hm σ τ, neg_ite, neg_zero]
    have hloc' : ∀ Z : Finset Λ, 1 < Metric.diam (Z : Set Λ) → - h Z = 0 := by
      intro Z hZ
      rw [hloc Z hZ, neg_zero]
    exact eq_44_iter (fun Z => - h Z) hherm' hsupp' hloc' B Y hB ⌊setDist X Y⌋₊ X hdist (-t) hnt
