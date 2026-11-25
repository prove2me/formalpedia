-- Prove2me | solution 1 for GlobalTheory.exists_short_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:27:16.33138+00:00
-- url     : https://prove2.me/submissions/e4e8ad3e-1622-4879-b6bb-f93eaca9be64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Theorems.Thm_GlobalTheory_ShortVectors_transference_rat
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_apply
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_self
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_isSymm
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_nonneg
import Theorems.Thm_GlobalTheory_ShortVectors_two_mul_le_traceHerm
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_nondegenerate
import Theorems.Thm_GlobalTheory_ShortVectors_finrank_eq
import Theorems.Thm_GlobalTheory_ShortVectors_exists_basis
import Theorems.Thm_GlobalTheory_DualFamily_span_eq_top
import Theorems.Thm_GlobalTheory_trace_dual_min


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ShortVectors
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) :
    ∃ v : Fin (2 * fdeg E * n) → Fin n → E, (∀ i, v i ∈ Λ) ∧ LinearIndependent ℚ v ∧ Submodule.span ℚ (Set.range v) = ⊤ ∧
      ∀ i (τ : E →+* ℂ), ∑ k, ‖τ (v i k)‖ ^ 2 ≤ (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) ^ 2 := by
  classical
  have hspan := DualFamily.span_eq_top Λ hfg hdual
  obtain ⟨b, hb⟩ := exists_basis Λ hfg hspan
  have hfin : finrank ℚ E = 2 * fdeg E := finrank_eq
  have hf : 0 < fdeg E := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    omega
  have hrd : 0 < rdE E := by
    unfold rdE dE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero E))) _
  have hF0 : (0 : ℝ) < fdeg E := by exact_mod_cast hf
  set lam : ℝ := Real.sqrt (2 * fdeg E) / rdE E with hlam_def
  have hlam : 0 < lam := div_pos (Real.sqrt_pos.mpr (by positivity)) hrd
  have hl2 : lam ^ 2 = 2 * fdeg E / rdE E ^ 2 := by
    rw [hlam_def, div_pow, Real.sq_sqrt (by positivity)]
  have hmin : ∀ u, u ≠ 0 → (∀ j, ∃ k : ℤ, traceHerm n u (b j) = k) →
      lam ^ 2 ≤ (traceHerm n u u : ℝ) := by
    intro u hu hj
    have htr : ∀ y ∈ Λ, ∃ k : ℤ, Algebra.trace ℚ E (herm 1 u y) = k := by
      intro y hy
      have hy' := (hb y).mpr hy
      clear hy
      simp only [← traceHerm_apply]
      induction hy' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact hj j
      | zero => exact ⟨0, by simp⟩
      | add x z _ _ hx hz =>
        obtain ⟨k1, h1⟩ := hx
        obtain ⟨k2, h2⟩ := hz
        exact ⟨k1 + k2, by rw [map_add, h1, h2]; push_cast; ring⟩
      | smul a x _ hx =>
        obtain ⟨k, h⟩ := hx
        exact ⟨a * k, by rw [map_zsmul, h, zsmul_eq_mul]; push_cast; ring⟩
    have h1 := trace_dual_min Λ hint hdual u hu htr
    rw [traceHerm_self, hl2]
    exact h1
  obtain ⟨v, hvΛ, hvli, hvB⟩ := transference_rat b (traceHerm n) (traceHerm_isSymm n)
    traceHerm_nonneg (traceHerm_nondegenerate n) lam hlam hmin
  refine ⟨v, fun i => (hb _).mp (hvΛ i), hvli, ?_, fun i τ => ?_⟩
  · exact hvli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, Module.finrank_eq_card_basis b, Fintype.card_fin])
  · have h2 := two_mul_le_traceHerm (v i) τ
    have h3 := hvB i
    have hF3 : ((fdeg E : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (fdeg E : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast ((fdeg E : ℝ) ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hF0.le,
        ← Real.rpow_natCast (fdeg E : ℝ) 3]
      norm_num
    have key : (((2 * fdeg E * n : ℕ) : ℝ) ^ 2 / lam) ^ 2 =
        2 * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) ^ 2 := by
      rw [div_pow, hl2, mul_pow, mul_pow, mul_pow, hF3]
      push_cast
      field_simp
    linarith
end GlobalTheory
