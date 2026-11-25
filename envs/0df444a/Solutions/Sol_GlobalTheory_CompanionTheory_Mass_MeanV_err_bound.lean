-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.err_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:24:10.325529+00:00
-- url     : https://prove2.me/submissions/9bba6172-be2f-42bf-b690-91a1b49c2ae2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlacesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProductDifferenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmallStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultipliableLocalFactorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorSandwichApproxStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EulerProductConvergenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalHaarMeasureSingletonStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeanValueFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_exists_zero_place
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_sum_comm
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_support_finite
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_tsum_ne_zero_eq_sum
import Theorems.Thm_GlobalTheory_T_euler_product_convergence_bound
import Theorems.Thm_GlobalTheory_T_exists_integral_multiple_bounded_places
import Theorems.Thm_GlobalTheory_T_finite_product_difference_bound
import Theorems.Thm_GlobalTheory_T_multipliable_local_factors
import Theorems.Thm_GlobalTheory_T_tail_sum_over_places_small
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV
namespace GlobalTheory.CompanionTheory.Mass.MeanV
theorem _root_.solution (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hG : Continuous G)
    (hGc : HasCompactSupport G) (hG0 : ∀ y, 0 ≤ G y) (hg0 : ∀ v y, 0 ≤ g v y)
    (hgS : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v))
    (hz : ∀ v, v ∉ S → ∀ s, s ∉ v.adicCompletionIntegers F → g v s = 0)
    (hb1 : ∀ v, v ∉ S → ∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ))
    (hb2 : ∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2)
    {η : ℝ} (hη : 0 < η) :
    ∃ T₀ : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T₀ ∧ ∀ T, T₀ ⊆ T → ∀ δ : ℝ, 0 < δ →
      |fullSum θ G g δ - truncSum θ G T g δ| ≤ η := by
  obtain ⟨N, hN, hNx⟩ := GlobalTheory.T.exists_integral_multiple_bounded_places F S (fun v => tsupport (g v)) (fun v hv => (hgS v hv).2)
  obtain ⟨C', hC'0, hcount⟩ := GlobalTheory.T.euler_product_convergence_bound hC F hF θ hθ (tsupport G) hGc N hN
  obtain ⟨MG, hMG⟩ := hGc.exists_bound_of_continuous hG
  have hmex : ∀ v, ∃ m : ℝ, 0 ≤ m ∧ (v ∈ S → ∀ s, g v s ≤ m) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨m, hm⟩ := (hgS v hv).2.exists_bound_of_continuous (hgS v hv).1
      exact ⟨|m|, abs_nonneg _, fun _ s => ((le_abs_self _).trans (hm s)).trans (le_abs_self _)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hv⟩
  choose m hm0 hm using hmex
  set M : ℝ := |MG| * ∏ v ∈ S, m v with hMdef
  have hM0 : 0 ≤ M := mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun v _ => hm0 v)
  have hden : 0 < M * C' + 1 := by positivity
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.tail_sum_over_places_small F C hC0 (η / (M * C' + 1)) (div_pos hη hden)
  refine ⟨T₁ ∪ S, Finset.subset_union_right, ?_⟩
  intro T hT δ hδ
  have hST : S ⊆ T := Finset.subset_union_right.trans hT
  have hT1 : T₁ ⊆ T := Finset.subset_union_left.trans hT
  have hfin := support_finite hC F hF θ hθ S (tsupport G) hGc (fun v => tsupport (g v))
    (fun v hv => (hgS v hv).2) δ hδ
  set B : Finset F := hfin.toFinset with hBdef
  have hBm : ∀ x ∈ B, x ≠ 0 ∧ x ∈ IntOut S ∧ θ δ * algebraMap F (Ainf F) x ∈ tsupport G ∧
      ∀ v ∈ S, algebraMap F (Fv F v) x ∈ tsupport (g v) := fun x hx => (hfin.mem_toFinset).1 hx
  have hB0 : ∀ x ∈ B, x ≠ 0 := fun x hx => (hBm x hx).1
  have hIT : ∀ x ∈ B, x ∈ IntOut T := fun x hx v hv => (hBm x hx).2.1 v (fun h => hv (hST h))
  have hMul : ∀ x : F, x ≠ 0 → Multipliable fun v => g v (algebraMap F (Fv F v) x) :=
    fun x hx => GlobalTheory.T.multipliable_local_factors F S C g hb2 x hx
  have hout : ∀ x, x ≠ 0 → x ∉ B → G (θ δ * algebraMap F (Ainf F) x) = 0 ∨
      ∃ v, g v (algebraMap F (Fv F v) x) = 0 ∧ ∀ T, S ⊆ T → x ∈ IntOut T → v ∈ T := by
    intro x hx hxB
    by_cases h1 : θ δ * algebraMap F (Ainf F) x ∈ tsupport G
    · right
      refine exists_zero_place S g hz fun h2 => hxB ?_
      exact (hfin.mem_toFinset).2 ⟨hx, h2.1, h1, h2.2⟩
    · left
      exact image_eq_zero_of_notMem_tsupport h1
  have e1 : ∑' β : {β : F // β ≠ 0}, G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1) =
      ∑ x ∈ B, G (θ δ * algebraMap F (Ainf F) x) * ∏' v, g v (algebraMap F (Fv F v) x) := by
    refine tsum_ne_zero_eq_sum (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏' v, g v (algebraMap F (Fv F v) x)) B hB0 ?_
    intro x hx hxB
    change G (θ δ * algebraMap F (Ainf F) x) * ∏' v, g v (algebraMap F (Fv F v) x) = 0
    rcases hout x hx hxB with h | ⟨v, hv, -⟩
    · rw [h, zero_mul]
    · rw [tprod_of_exists_eq_zero (f := fun v => g v (algebraMap F (Fv F v) x)) ⟨v, hv⟩, mul_zero]
  have e2 : ∑' β : {β : F // β ≠ 0}, (IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x)) β.1 =
      ∑ x ∈ B, G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x) := by
    rw [tsum_ne_zero_eq_sum ((IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x))) B hB0 ?_]
    · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (hIT x hx) _
    · intro x hx hxB
      by_cases hxT : x ∈ IntOut T
      · rw [Set.indicator_of_mem hxT]
        rcases hout x hx hxB with h | ⟨v, hv, hvT⟩
        · simp only [h, zero_mul]
        · rw [Finset.prod_eq_zero (hvT T hST hxT) hv, mul_zero]
      · exact Set.indicator_of_notMem hxT _
  have hpow : 0 ≤ δ ^ Module.finrank ℚ F := pow_nonneg hδ.le _

  have key : ∀ U : Finset (HeightOneSpectrum (𝓞 F)), T ⊆ U →
      δ ^ Module.finrank ℚ F * ∑ x ∈ B, |G (θ δ * algebraMap F (Ainf F) x) *
        (∏ v ∈ U, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x))| ≤ η := by
    intro U hU
    have hsub : T \ S ⊆ U \ S := Finset.sdiff_subset_sdiff hU le_rfl
    have hx1 : ∀ x ∈ B, |G (θ δ * algebraMap F (Ainf F) x) *
        (∏ v ∈ U, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x))| ≤
        M * ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S, ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| := by
      intro x hx
      have hU' := Finset.prod_sdiff (f := fun v => g v (algebraMap F (Fv F v) x)) (hST.trans hU)
      have hT' := Finset.prod_sdiff (f := fun v => g v (algebraMap F (Fv F v) x)) hST
      have hexp := GlobalTheory.T.finite_product_difference_bound _ (fun v => g v (algebraMap F (Fv F v) x)) (T \ S) (U \ S) hsub
      have hfac : G (θ δ * algebraMap F (Ainf F) x) *
          (∏ v ∈ U, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x)) =
          (G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ S, g v (algebraMap F (Fv F v) x)) *
          (∏ v ∈ U \ S, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T \ S, g v (algebraMap F (Fv F v) x)) := by
        rw [← hU', ← hT']; ring
      have hGS0 : 0 ≤ G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ S, g v (algebraMap F (Fv F v) x) :=
        mul_nonneg (hG0 _) (Finset.prod_nonneg fun v _ => hg0 v _)
      have hGS : G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ S, g v (algebraMap F (Fv F v) x) ≤ M := by
        refine mul_le_mul ?_ (Finset.prod_le_prod (fun v _ => hg0 v _) fun v hv => hm v hv _)
          (Finset.prod_nonneg fun v _ => hg0 v _) (abs_nonneg _)
        exact ((le_abs_self _).trans (hMG _)).trans (le_abs_self _)
      rw [hfac, abs_mul, abs_of_nonneg hGS0]
      exact mul_le_mul hGS hexp (abs_nonneg _) hM0
    have hfilter : ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S, ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ≤
        η / (M * C' + 1) := by
      refine le_trans (le_of_eq ?_) (hT₁ T hT1 (U \ S))
      refine Finset.sum_congr (Finset.filter_congr ?_) fun _ _ => rfl
      intro D hD
      have hDU := Finset.mem_powerset.1 hD
      refine not_congr ⟨fun h => h.trans Finset.sdiff_subset, fun h v hv => ?_⟩
      exact Finset.mem_sdiff.2 ⟨h hv, (Finset.mem_sdiff.1 (hDU hv)).2⟩
    have hcnt : ∀ D ∈ (U \ S).powerset.filter (fun D => ¬ D ⊆ T \ S),
        δ ^ Module.finrank ℚ F * ∑ x ∈ B, ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| ≤
          C' * ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
      intro D hD
      have hDU := Finset.mem_powerset.1 (Finset.mem_filter.1 hD).1
      have hdis : Disjoint D S := by
        rw [Finset.disjoint_left]
        intro v hv hvS
        exact (Finset.mem_sdiff.1 (hDU hv)).2 hvS
      refine hcount S C g hC0 (fun v hv => ⟨hb1 v hv, hb2 v hv⟩) δ hδ D hdis B ?_
      intro x hx
      obtain ⟨h0, h1, h2, h3⟩ := hBm x hx
      exact ⟨h0, h1, hNx x h1 h3, h2⟩
    calc δ ^ Module.finrank ℚ F * ∑ x ∈ B, |G (θ δ * algebraMap F (Ainf F) x) *
          (∏ v ∈ U, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x))|
        ≤ δ ^ Module.finrank ℚ F * ∑ x ∈ B, M * ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S,
            ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hx1) hpow
      _ = M * ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S, δ ^ Module.finrank ℚ F *
            ∑ x ∈ B, ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| := by
          rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun D _ => ?_
          ring
      _ ≤ M * ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S, C' *
            ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcnt) hM0
      _ = M * C' * ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S,
            ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ M * C' * (η / (M * C' + 1)) := mul_le_mul_of_nonneg_left hfilter (mul_nonneg hM0 hC'0)
      _ ≤ η := by
          rw [mul_div_assoc', div_le_iff₀ hden]
          nlinarith [mul_nonneg hM0 hC'0]

  have hlim : Tendsto (fun U : Finset (HeightOneSpectrum (𝓞 F)) => δ ^ Module.finrank ℚ F * ∑ x ∈ B,
      |G (θ δ * algebraMap F (Ainf F) x) *
        (∏ v ∈ U, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x))|) atTop
      (𝓝 (δ ^ Module.finrank ℚ F * ∑ x ∈ B, |G (θ δ * algebraMap F (Ainf F) x) *
        (∏' v, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x))|)) := by
    refine Tendsto.const_mul _ (tendsto_finset_sum _ fun x hx => ?_)
    exact (((hMul x (hB0 x hx)).hasProd.sub_const _).const_mul _).abs
  have hfinal := le_of_tendsto hlim ((eventually_ge_atTop T).mono fun U hU => key U hU)
  unfold fullSum truncSum
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_nonneg hpow, ← Finset.sum_sub_distrib]
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hpow) ?_
  refine le_trans (le_of_eq ?_) hfinal
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_sub]
end GlobalTheory.CompanionTheory.Mass.MeanV
