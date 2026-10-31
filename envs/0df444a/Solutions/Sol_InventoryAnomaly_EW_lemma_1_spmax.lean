-- Prove2me | solution 1 for InventoryAnomaly.EW.lemma_1_spmax
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:58:35.874983+00:00
-- url     : https://prove2.me/submissions/8271601f-387c-4d61-9365-0c0912b2cb90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model
import Theorems.Thm_InventoryAnomaly_EW_lemma_2
import Theorems.Thm_InventoryAnomaly_EW_lemma_17

open MeasureTheory ProbabilityTheory
open scoped NNReal
open InventoryAnomaly.EW

lemma IA1s_model_mono {d : ℕ} {I : Instance d} {cM cA Csp Csp' K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) (hle : Csp' ≤ Csp) : I.Model cM cA Csp' K L μ := by
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hμ : 0 ≤ μ := by
    have h := hI.incoh_U ⟨0, hn0⟩
    have h0 : 0 ≤ ∑ k, I.U ⟨0, hn0⟩ k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_contra hneg'
    have hneg : μ < 0 := lt_of_not_ge hneg'
    have hr' : (0 : ℝ) < I.r := by exact_mod_cast hI.r_pos
    have hn' : (0 : ℝ) < I.n := by exact_mod_cast hn0
    have : μ * I.r / I.n < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hr') hn'
    linarith
  refine { hI with sparsity := ?_ }
  have hX : 0 ≤ Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m := by
    have : 0 ≤ Real.log I.m := Real.log_natCast_nonneg _
    positivity
  have h := hI.sparsity
  calc Csp' * Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m
      = Csp' * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m) := by ring
    _ ≤ Csp * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m) :=
        mul_le_mul_of_nonneg_right hle hX
    _ = _ := by ring
    _ ≤ _ := h

lemma IA1s_spmax_mono {d : ℕ} {I : Instance d} {cM cA Csp Csp' K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) (hS : I.SparsityMax hI.r_pos Csp μ L) (hle : Csp' ≤ Csp) :
    I.SparsityMax hI.r_pos Csp' μ L := by
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hm0 : 0 < I.m := by have := hI.two_le_m; omega
  have hL : 0 ≤ L := (abs_nonneg _).trans (hI.max_ub ⟨0, hn0⟩ ⟨0, hm0⟩)
  have hμ : 0 ≤ μ := by
    have h := hI.incoh_U ⟨0, hn0⟩
    have h0 : 0 ≤ ∑ k, I.U ⟨0, hn0⟩ k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_contra hneg'
    have hneg : μ < 0 := lt_of_not_ge hneg'
    have hr' : (0 : ℝ) < I.r := by exact_mod_cast hI.r_pos
    have hn' : (0 : ℝ) < I.n := by exact_mod_cast hn0
    have : μ * I.r / I.n < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hr') hn'
    linarith
  intro i₀ j₀ hmax
  have h := hS i₀ j₀ hmax
  have hM0 : 0 ≤ I.Mstar i₀ j₀ := hI.nonneg i₀ j₀
  have hX : 0 ≤ Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
      (I.Mstar i₀ j₀ * Real.sqrt I.m) := by
    have : 0 ≤ Real.log I.m := Real.log_natCast_nonneg _
    positivity
  calc Csp' * Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
        (I.Mstar i₀ j₀ * Real.sqrt I.m)
      = Csp' * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
        (I.Mstar i₀ j₀ * Real.sqrt I.m)) := by ring
    _ ≤ Csp * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
        (I.Mstar i₀ j₀ * Real.sqrt I.m)) := mul_le_mul_of_nonneg_right hle hX
    _ = _ := by ring
    _ ≤ _ := h


lemma IA1s_mu_ge_one {d : ℕ} {I : Instance d} {cM cA Csp K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) : 1 ≤ μ := by
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hcol : ∀ k, ∑ i, I.U i k ^ 2 = 1 := by
    intro k
    have h := congrFun (congrFun hI.U_orth k) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    simpa [sq] using h
  have hsum : ∑ i, ∑ k, I.U i k ^ 2 = I.r := by
    rw [Finset.sum_comm]; simp [hcol]
  have hle : ∑ i, ∑ k, I.U i k ^ 2 ≤ ∑ _i : Fin I.n, μ * I.r / I.n :=
    Finset.sum_le_sum fun i _ => hI.incoh_U i
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  have hn' : (0 : ℝ) < I.n := by exact_mod_cast hn0
  have hr' : (0 : ℝ) < I.r := by exact_mod_cast hI.r_pos
  rw [mul_div_cancel₀ _ hn'.ne'] at hle
  nlinarith

lemma IA1s_kappa_ge_one {d : ℕ} {I : Instance d} {cM cA Csp K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) : 1 ≤ I.κ hI.r_pos := by
  unfold Instance.κ
  have h1 := hI.σ_pos ⟨I.r - 1, by have := hI.r_pos; omega⟩
  have h2 : I.σ ⟨I.r - 1, by have := hI.r_pos; omega⟩ ≤ I.σ ⟨0, hI.r_pos⟩ :=
    hI.σ_anti (Fin.mk_le_mk.2 (Nat.zero_le _))
  rw [one_le_div h1]; exact h2

/-- A large sparsity constant forces `log m` to be large. -/
lemma IA1s_log_large {d : ℕ} {I : Instance d} {cM cA Csp K L μ : ℝ} (A : ℝ)
    (hI : I.Model cM cA Csp K L μ) (hCsp : 4 * Real.exp (A / 2) ≤ Csp) : A ≤ Real.log I.m := by
  by_contra hlt
  push_neg at hlt
  have hm2 : (2 : ℝ) ≤ I.m := by exact_mod_cast hI.two_le_m
  have hm0 : (0 : ℝ) < I.m := by linarith
  have hμ := IA1s_mu_ge_one hI
  have hκ := IA1s_kappa_ge_one hI
  have hr : (1 : ℝ) ≤ I.r := by exact_mod_cast hI.r_pos
  have hpO1 : (I.pO : ℝ) ≤ 1 := by exact_mod_cast hI.pO_le
  have hq1 : Real.sqrt I.pO ≤ 1 := by simpa using Real.sqrt_le_sqrt hpO1
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log I.m := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log I.m := Real.log_le_log (by norm_num) hm2
    linarith
  have hX : (1 / 4 : ℝ) ≤ Real.log I.m ^ ((3 : ℝ) / 2) := by
    have h1 : ((1 / 2 : ℝ)) ^ ((3 : ℝ) / 2) ≤ Real.log I.m ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow (by norm_num) hlog2 (by norm_num)
    have h2 : ((1 / 2 : ℝ)) ^ (2 : ℝ) ≤ ((1 / 2 : ℝ)) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    have h3 : ((1 / 2 : ℝ)) ^ (2 : ℝ) = 1 / 4 := by rw [Real.rpow_two]; norm_num
    linarith
  have hs : Real.sqrt I.m < Real.exp (A / 2) := by
    by_contra hge
    push_neg at hge
    have : Real.exp (A / 2) ^ 2 ≤ Real.sqrt I.m ^ 2 := by gcongr
    rw [Real.sq_sqrt hm0.le, ← Real.exp_nat_mul] at this
    have := Real.log_le_log (Real.exp_pos _) this
    rw [Real.log_exp] at this
    push_cast at this
    linarith
  have hs0 : 0 < Real.sqrt I.m := Real.sqrt_pos.2 hm0
  have hsp := hI.sparsity
  have hκ2 : 1 ≤ I.κ hI.r_pos ^ 2 := one_le_pow₀ hκ
  have hprod : 1 ≤ μ * I.r * I.κ hI.r_pos ^ 2 := by
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ μ * I.r * I.κ hI.r_pos ^ 2 := by gcongr
  have hCpos : 0 < Csp := lt_of_lt_of_le (by positivity) hCsp
  have hbig : Real.sqrt I.m < Csp * Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 := by
    calc Real.sqrt I.m < Real.exp (A / 2) := hs
      _ = 4 * Real.exp (A / 2) * (1 / 4) := by ring
      _ ≤ Csp * Real.log I.m ^ ((3 : ℝ) / 2) := mul_le_mul hCsp hX (by norm_num) hCpos.le
      _ = Csp * Real.log I.m ^ ((3 : ℝ) / 2) * 1 := by ring
      _ ≤ Csp * Real.log I.m ^ ((3 : ℝ) / 2) * (μ * I.r * I.κ hI.r_pos ^ 2) := by
          have : 0 ≤ Real.log I.m ^ ((3 : ℝ) / 2) := by linarith
          gcongr
      _ = _ := by ring
  rw [div_le_iff₀ hs0] at hsp
  nlinarith

lemma IA1s_coord_le {D : ℕ} (v : EuclideanSpace ℝ (Fin D)) (i : Fin D) : |v i| ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  apply Real.le_sqrt_of_sq_le
  have := Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using this

theorem solution (d : ℕ) (cM cA CRC : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1)
    (hCRC : 0 < CRC) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        I.Regular hI.r_pos cA CRC K L μ →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω |
          ‖θhat (I.obs ω) - I.θstar‖ ≤ C * (K + L) * I.δ' hI.r_pos μ L} := by
  obtain ⟨Cs2, C2, C2', h2s, h2C, h2C', H2⟩ := lemma_2 d cM cA hcM hcA hcA1
  set A : ℝ := 4 * ((d : ℝ) + 1) * CRC ^ 3 * C2 + 2 * CRC * C2 + 1 with hA
  refine ⟨max Cs2 (4 * Real.exp (A / 2)), 2 * CRC * C2, C2', lt_max_of_lt_left h2s,
    by positivity, h2C', ?_⟩
  intro I K L μ hI hS hReg svdr θhat hsvd hsel
  have hI2 := IA1s_model_mono hI (le_max_left Cs2 (4 * Real.exp (A / 2)))
  have E2 := H2 I K L μ hI2 (IA1s_spmax_mono hI hS (le_max_left _ _)) svdr θhat hsvd hsel
  have hlogA : A ≤ Real.log I.m := IA1s_log_large A hI (le_max_right _ _)
  -- elementary facts
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hm0 : 0 < I.m := by have := hI.two_le_m; omega
  have hL : 0 ≤ L := (abs_nonneg _).trans (hI.max_ub ⟨0, hn0⟩ ⟨0, hm0⟩)
  have hK : 0 ≤ K := by
    have := hI.smooth 0 (I.αstar, 0) ⟨hI.α_mem, Set.mem_Ici.2 le_rfl⟩ (I.αstar, 1)
      ⟨hI.α_mem, Set.mem_Ici.2 zero_le_one⟩
    have hd : dist ((I.αstar, (0 : ℝ))) (I.αstar, (1 : ℝ)) = 1 := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [hd, mul_one] at this
    exact (abs_nonneg _).trans this
  have hμ := IA1s_mu_ge_one hI
  have hκ := IA1s_kappa_ge_one hI
  have hδ0 : 0 ≤ I.δ' hI.r_pos μ L := by
    unfold Instance.δ'
    have : (0 : ℝ) ≤ I.r := Nat.cast_nonneg _
    have : 0 ≤ I.κ hI.r_pos := by linarith
    have : 0 ≤ μ := by linarith
    positivity
  set e := (K + L) * I.δ' hI.r_pos μ L with he
  have he0 : 0 ≤ e := mul_nonneg (by linarith) hδ0
  have hlog0 : 0 ≤ Real.log I.m := Real.log_natCast_nonneg _
  have hA0 : 0 ≤ 2 * CRC * C2 := by positivity
  have hA1 : 2 * CRC * C2 ≤ Real.log I.m := by
    have : 0 ≤ 4 * ((d : ℝ) + 1) * CRC ^ 3 * C2 := by positivity
    linarith
  have hA2 : 4 * ((d : ℝ) + 1) * CRC ^ 3 * C2 < Real.log I.m := by
    have : 0 ≤ 2 * CRC * C2 := by positivity
    linarith
  unfold Instance.Regular at hReg
  obtain ⟨hC1F, hinj, hballt, hJt, Jinv, hJ1, hJ2, hJn⟩ := hReg
  set δt := I.δ' hI.r_pos μ L * (K + L) * Real.log I.m with hδt
  have hδt : δt = e * Real.log I.m := by rw [hδt, he]; ring
  have hδt0 : 0 ≤ δt := by rw [hδt]; positivity
  have hθs : I.θstar ∈ I.Θ cA := hballt (Metric.mem_closedBall_self hδt0)
  have hrad : 2 * CRC * (C2 * (K + L) * I.δ' hI.r_pos μ L) ≤ δt := by
    rw [hδt, show C2 * (K + L) * I.δ' hI.r_pos μ L = C2 * e by rw [he]; ring]
    calc 2 * CRC * (C2 * e) = (2 * CRC * C2) * e := by ring
      _ ≤ Real.log I.m * e := by gcongr
      _ = e * Real.log I.m := by ring
  have hsub : Metric.closedBall I.θstar (2 * CRC * (C2 * (K + L) * I.δ' hI.r_pos μ L)) ⊆
      Metric.closedBall I.θstar δt := Metric.closedBall_subset_closedBall hrad
  have hJ : ∀ θ ∈ Metric.closedBall I.θstar (2 * CRC * (C2 * (K + L) * I.δ' hI.r_pos μ L)),
      ∀ i j : Fin (d + 1),
      |(fderivWithin ℝ I.F (I.Θ cA) θ - fderivWithin ℝ I.F (I.Θ cA) I.θstar)
        (EuclideanSpace.single j 1) i| ≤ CRC / δt * ‖θ - I.θstar‖ := by
    intro θ hθ i j
    refine (IA1s_coord_le _ i).trans ?_
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [PiLp.norm_single, norm_one, mul_one]
    exact hJt θ (hsub hθ)
  have hsmall : 2 * Real.sqrt (((d + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ)) * (CRC / δt) * CRC ^ 2 *
      (C2 * (K + L) * I.δ' hI.r_pos μ L) < 1 / 2 := by
    rw [Real.sqrt_mul_self (Nat.cast_nonneg _),
      show C2 * (K + L) * I.δ' hI.r_pos μ L = C2 * e by rw [he]; ring, hδt]
    push_cast
    rcases lt_or_eq_of_le he0 with hepos | hezero
    · have hlogpos : 0 < Real.log I.m := lt_of_le_of_lt (by positivity) hA2
      have : 2 * ((d : ℝ) + 1) * (CRC / (e * Real.log I.m)) * CRC ^ 2 * (C2 * e) =
          2 * ((d : ℝ) + 1) * CRC ^ 3 * C2 / Real.log I.m := by
        field_simp
      rw [this, div_lt_iff₀ hlogpos]
      linarith
    · rw [← hezero]; simp
  have key := lemma_17 I.F (I.Θ cA) I.θstar (CRC / δt) CRC (C2 * (K + L) * I.δ' hI.r_pos μ L)
    hC1F hinj hθs (hsub.trans hballt) hJ Jinv ⟨hJ1, hJ2⟩ hJn hsmall
  have hP : IsProbabilityMeasure I.law := by unfold Instance.law; infer_instance
  refine E2.trans (measureReal_mono ?_)
  intro ω hω
  have := key (θhat (I.obs ω)) (hsel _).1 hω
  show ‖θhat (I.obs ω) - I.θstar‖ ≤ 2 * CRC * C2 * (K + L) * I.δ' hI.r_pos μ L
  calc _ ≤ _ := this
    _ = _ := by ring
