-- Prove2me | solution 1 for GlobalTheory.FrameNet.exists_net_of_matrices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:08:49.899243+00:00
-- url     : https://prove2.me/submissions/f866441a-d95b-42b8-8c5d-0f07e5e744b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres
import Theorems.Thm_GlobalTheory_FrameNet_norm_det_le
import Theorems.Thm_GlobalTheory_FrameNet_norm_mul_inv_sub_one_le
import Theorems.Thm_GlobalTheory_FrameNet_norm_sub_le_of_cell_eq
import Theorems.Thm_GlobalTheory_FrameNet_cell_mem
import Theorems.Thm_GlobalTheory_FrameNet_card_Icc_floor_le
import Theorems.Thm_GlobalTheory_FrameNet_exists_finset_meeting_fibres
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open GlobalTheory GlobalTheory.FrameNet
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
noncomputable section
namespace GlobalTheory.FrameNet
theorem _root_.solution {α ι : Type*} [Fintype ι] {r : ℕ} (O : Set α)
    (m : α → ι → Matrix (Fin r) (Fin r) ℂ) (D : ι → ℝ) (hD0 : ∀ τ, 0 < D τ) (hD : 1 ≤ ∏ τ, D τ)
    {B η : ℝ} (hB : 1 ≤ B) (hη0 : 0 < η) (hη : η ≤ 1)
    (hm : ∀ x ∈ O, ∀ τ i k, ‖m x τ i k‖ ^ 2 ≤ B) (hdet : ∀ x ∈ O, ∀ τ, ‖(m x τ).det‖ = D τ) :
    ∃ N : Finset α, (N : Set α) ⊆ O ∧
      (N.card : ℝ) ≤ (6 * (r : ℝ) ^ 2 / η * ((r : ℝ) * B) ^ r) ^ (2 * Fintype.card ι * r ^ 2) ∧
      ∀ x ∈ O, ∃ y ∈ N, ∀ τ a b,
        ‖(m x τ * (m y τ)⁻¹) a b - (if a = b then 1 else 0)‖ ≤ η := by
  classical
  rcases O.eq_empty_or_nonempty with hO | ⟨x0, hx0⟩
  · refine ⟨∅, by simp, ?_, fun x hx => by simp [hO] at hx⟩
    rw [Finset.card_empty, Nat.cast_zero]
    apply pow_nonneg
    exact mul_nonneg (div_nonneg (by positivity) hη0.le)
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) _)
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact ⟨{x0}, by simpa using hx0, by simp, fun x _ => ⟨x0, by simp, fun τ a => a.elim0⟩⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt B := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hB
  have hs0 : 0 < s := by linarith
  have hsB : s ^ 2 = B := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hent : ∀ x ∈ O, ∀ τ i k, ‖m x τ i k‖ ≤ s := fun x hx τ i k => by
    have h := Real.abs_le_sqrt (hm x hx τ i k)
    rwa [abs_norm, ← hs] at h
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hDM : ∀ τ, D τ ≤ (r : ℝ) ^ r * s ^ r := fun τ => by
    rw [← hdet x0 hx0 τ]; exact norm_det_le hs0.le (hent x0 hx0 τ)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * (r : ℝ) ^ (r + 1) * s ^ r := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ι → ℝ, ∀ τ, δ τ = η * D τ / c := ⟨_, fun _ => rfl⟩
  have hδ0 : ∀ τ, 0 < δ τ := fun τ => by rw [hδ]; exact div_pos (mul_pos hη0 (hD0 τ)) hc0
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ,
      Q = 4 * (r : ℝ) ^ (r + 1) * s ^ (r + 1) / η + (r : ℝ) ^ r * s ^ r := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; exact add_pos (div_pos (by positivity) hη0) (by positivity)
  have hcnt : ∀ τ, ((Finset.Icc (0 : ℤ) ⌊2 * s / δ τ⌋).card : ℝ) ≤ Q / D τ := by
    intro τ
    have hDτ := hD0 τ
    refine (card_Icc_floor_le (div_nonneg (by linarith) (hδ0 τ).le)).trans ?_
    have e : 2 * s / δ τ = (4 * (r : ℝ) ^ (r + 1) * s ^ (r + 1) / η) / D τ := by
      have := hη0.ne'; have := hDτ.ne'; have := hr0.ne'; have := hs0.ne'
      rw [hδ, hc]; field_simp; ring
    rw [e, hQ, add_div]
    linarith [(one_le_div hDτ).mpr (hDM τ)]
  have hQb : Q ≤ 6 * (r : ℝ) ^ 2 / η * ((r : ℝ) * B) ^ r := by
    have e1 : ((r : ℝ) * B) ^ r = (r : ℝ) ^ r * s ^ (2 * r) := by rw [mul_pow, ← hsB, ← pow_mul]
    have p1 : (r : ℝ) ^ (r + 1) ≤ (r : ℝ) ^ r * r ^ 2 := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have p2 : s ^ (r + 1) ≤ s ^ (2 * r) := pow_le_pow_right₀ hs1 (by omega)
    have p3 : s ^ r ≤ s ^ (2 * r) := pow_le_pow_right₀ hs1 (by omega)
    have p4 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hX : 0 ≤ (r : ℝ) ^ r * s ^ (2 * r) := by positivity
    have a1 : 4 * (r : ℝ) ^ (r + 1) * s ^ (r + 1) ≤ 4 * ((r : ℝ) ^ r * r ^ 2) * s ^ (2 * r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left p1 (by norm_num)) p2 (by positivity) (by positivity)
    have b1 : η * ((r : ℝ) ^ r * s ^ r) ≤ 1 * ((r : ℝ) ^ r * s ^ (2 * r)) :=
      mul_le_mul hη (mul_le_mul_of_nonneg_left p3 (by positivity)) (by positivity) zero_le_one
    have b2 := mul_le_mul_of_nonneg_right p4 hX
    rw [hQ, e1]
    have e2 : 4 * (r : ℝ) ^ (r + 1) * s ^ (r + 1) / η + (r : ℝ) ^ r * s ^ r
        = (4 * (r : ℝ) ^ (r + 1) * s ^ (r + 1) + η * ((r : ℝ) ^ r * s ^ r)) / η := by
      rw [add_div, mul_div_cancel_left₀ _ hη0.ne']
    have e3 : 6 * (r : ℝ) ^ 2 / η * ((r : ℝ) ^ r * s ^ (2 * r))
        = (6 * ((r : ℝ) ^ r * r ^ 2) * s ^ (2 * r)) / η := by ring
    rw [e2, e3]
    apply div_le_div_of_nonneg_right _ hη0.le
    nlinarith
  let g : α → ι → Fin r → Fin r → ℤ × ℤ := fun x τ i k => cell s (δ τ) (m x τ i k)
  let S : Finset (ι → Fin r → Fin r → ℤ × ℤ) :=
    Fintype.piFinset fun τ => Fintype.piFinset fun _ : Fin r => Fintype.piFinset fun _ : Fin r =>
      Finset.Icc (0 : ℤ) ⌊2 * s / δ τ⌋ ×ˢ Finset.Icc (0 : ℤ) ⌊2 * s / δ τ⌋
  have hgS : ∀ x ∈ O, g x ∈ S := by
    intro x hx
    simp only [S, g, Fintype.mem_piFinset]
    intro τ i k
    exact cell_mem (hδ0 τ) (hent x hx τ i k)
  obtain ⟨N, hNO, hNcard, hNcov⟩ := exists_finset_meeting_fibres O g S hgS
  refine ⟨N, hNO, ?_, ?_⟩
  · have hS : (S.card : ℝ) = ∏ τ, ((Finset.Icc (0 : ℤ) ⌊2 * s / δ τ⌋).card : ℝ) ^ (2 * r ^ 2) := by
      simp only [S, Fintype.card_piFinset, Finset.card_product, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      push_cast
      exact Finset.prod_congr rfl fun τ _ => by ring
    have hPD : 0 ≤ ∏ τ, D τ := Finset.prod_nonneg fun τ _ => (hD0 τ).le
    calc (N.card : ℝ) ≤ S.card := by exact_mod_cast hNcard
      _ = ∏ τ, ((Finset.Icc (0 : ℤ) ⌊2 * s / δ τ⌋).card : ℝ) ^ (2 * r ^ 2) := hS
      _ ≤ ∏ τ, (Q / D τ) ^ (2 * r ^ 2) :=
          Finset.prod_le_prod (fun τ _ => by positivity)
            (fun τ _ => pow_le_pow_left₀ (Nat.cast_nonneg _) (hcnt τ) _)
      _ = (Q ^ Fintype.card ι / ∏ τ, D τ) ^ (2 * r ^ 2) := by
          rw [Finset.prod_pow, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
      _ ≤ (Q ^ Fintype.card ι) ^ (2 * r ^ 2) := by
          apply pow_le_pow_left₀ (div_nonneg (pow_nonneg hQ0.le _) hPD)
          exact div_le_self (pow_nonneg hQ0.le _) hD
      _ = Q ^ (2 * Fintype.card ι * r ^ 2) := by rw [← pow_mul]; congr 1; ring
      _ ≤ _ := pow_le_pow_left₀ hQ0.le hQb _
  · intro x hx
    obtain ⟨y, hyN, hxy⟩ := hNcov x hx
    have hy := hNO hyN
    refine ⟨y, hyN, fun τ a b => ?_⟩
    have hcell : ∀ i k, ‖m x τ i k - m y τ i k‖ ≤ 2 * δ τ := fun i k =>
      norm_sub_le_of_cell_eq (hδ0 τ) (congrFun (congrFun (congrFun hxy τ) i) k)
    have hdy : (m y τ).det ≠ 0 := by
      intro h0
      have h1 := hdet y hy τ
      rw [h0, norm_zero] at h1
      exact (hD0 τ).ne h1
    have key := norm_mul_inv_sub_one_le hs1 (hent y hy τ) hdy hcell a b
    rw [hdet y hy τ] at key
    refine key.trans (le_of_eq ?_)
    have := hη0.ne'; have := (hD0 τ).ne'; have := hr0.ne'; have := hs0.ne'
    rw [hδ, hc]
    field_simp
    ring
end GlobalTheory.FrameNet
