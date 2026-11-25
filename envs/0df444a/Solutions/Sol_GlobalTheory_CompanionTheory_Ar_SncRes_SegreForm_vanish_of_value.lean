-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.vanish_of_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:57.080915+00:00
-- url     : https://prove2.me/submissions/0d9de367-d77a-4cb2-95e9-e8740026a394

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StandardSmoothChartOfNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SncRes_SegreForm_aeval_const_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SncRes_SegreForm_eval_map_int
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SncRes_SegreForm_aeval_eq_prod_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SncRes_SegreForm_mConeMap_segre
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTrdeg_mConeMap_of_isMultiHomog_42bb4e513f85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_mConeMap_of_isMultiHomog_507fb917434b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncRes GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {N : ℕ} (y : (Σ k, ι k) → Ω) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
namespace GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
theorem _root_.solution (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {β : MRing ι} {b : K → ℕ} (hb : IsMultiHomog β b)
    {n : ℕ} {m : ℤ} {G : MvPolynomial (Fin (N + 1)) ℤ} (hG : G.IsHomogeneous n)
    (hval : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) G =
      (m : Ω) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hβ : evC z β = 0) :
    (∏ k, z ⟨k, E c₀ k⟩) = 0 ∨ aeval (fun j => ∏ k, z ⟨k, E j k⟩) G = 0 := by
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hx : aeval (fun j => ∏ k, y ⟨k, E j k⟩) G * ∏ k, y ⟨k, E c₀ k⟩ ^ b k =
      (m : Ω) * aeval y β * (∏ k, y ⟨k, E c₀ k⟩) ^ n := by
    have e : (fun j => ∏ k, y ⟨k, E j k⟩) = fun j => (∏ k, y ⟨k, E c₀ k⟩) *
        ((∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) :=
      funext fun j => (mul_div_cancel₀ _ h0).symm
    rw [e, aeval_const_mul hG, hval, aeval_eq_prod_mul y E c₀ hc hb]
    ring
  let P₁ : MRing ι := aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) G * ∏ k, (X ⟨k, E c₀ k⟩ : MRing ι) ^ b k
  let P₂ : MRing ι := C m * β * (∏ k, (X ⟨k, E c₀ k⟩ : MRing ι)) ^ n
  have hmem : P₁ - P₂ ∈ mCoordIdeal y := by
    refine RingHom.mem_ker.2 ?_
    have hG' : mConeMap y (aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) G) =
        (∏ k, (X k : MvPolynomial K Ω)) ^ n * C (aeval (fun j => ∏ k, y ⟨k, E j k⟩) G) := by
      rw [comp_aeval_apply]
      simp only [mConeMap_segre]
      rw [aeval_const_mul hG]
      congr 1
      exact (comp_aeval_apply _ (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω)) G).symm
    have hX : mConeMap y (∏ k, (X ⟨k, E c₀ k⟩ : MRing ι) ^ b k) =
        (∏ k, (X k : MvPolynomial K Ω) ^ b k) * C (∏ k, y ⟨k, E c₀ k⟩ ^ b k) := by
      simp only [map_prod, map_pow, mConeMap, aeval_X, mul_pow, Finset.prod_mul_distrib]
      rw [mul_comm]
    have hC : mConeMap y (C m) = C (m : Ω) := by
      simp [mConeMap]
    have hS := mConeMap_segre y E c₀
    simp only [P₁, P₂, map_sub, map_mul, map_pow, hG', hX, hC, hS,
      GroundTheory.Heights₂.Heights.LowerBoundFree.mConeMap_of_isMultiHomog y hb]
    rw [sub_eq_zero]
    have := congrArg (C : Ω →+* MvPolynomial K Ω) hx
    simp only [map_mul, map_pow] at this
    calc _ = (∏ k, (X k : MvPolynomial K Ω)) ^ n * (∏ k, (X k : MvPolynomial K Ω) ^ b k) *
          (C (aeval (fun j => ∏ k, y ⟨k, E j k⟩) G) * C (∏ k, y ⟨k, E c₀ k⟩ ^ b k)) := by ring
      _ = _ := by rw [this]; ring
  have hzero := hz.2 _ hmem
  have hev : aeval z (P₁ - P₂) = 0 := by rw [← eval_map_int]; exact hzero
  have hβ' : aeval z β = 0 := by rw [← eval_map_int]; exact hβ
  have hP : aeval (fun j => ∏ k, z ⟨k, E j k⟩) G * ∏ k, z ⟨k, E c₀ k⟩ ^ b k = 0 := by
    simp only [P₁, P₂, map_sub, map_mul, map_pow, map_prod, aeval_X, hβ', comp_aeval_apply] at hev
    simpa using hev
  rcases mul_eq_zero.1 hP with h | h
  · exact Or.inr h
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    refine Or.inl (Finset.prod_eq_zero_iff.2 ⟨k, Finset.mem_univ _, ?_⟩)
    by_contra h'
    exact pow_ne_zero _ h' hk
end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
