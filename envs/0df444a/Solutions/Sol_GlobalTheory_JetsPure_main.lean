-- Prove2me | solution 1 for GlobalTheory.JetsPure.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:56.052218+00:00
-- url     : https://prove2.me/submissions/79ed3855-2ec9-4bba-8830-6db7b05a38a4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_PointwiseNormConstantSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SumMultiLtSucc
import Theorems.Thm_GlobalTheory_JetsPure_monomial_isBigO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_mem_multiIndicesBelow_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_taylor_expansion_local_coordinates
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.JetsPure
open Filter Asymptotics
open MeasureTheory Topology Filter Asymptotics
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.JetsPure
namespace _root_.GlobalTheory.JetsPure
theorem _root_.solution : ∀ (J I : Type) [Fintype I] (D T a : ℕ),
    a ≤ T + 1 → ∀ (n : J → ℕ) (e : ∀ p, Fin (n p) ≃ Fin D)
    (f w0 : ∀ p, _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ) (s : ∀ p, Fin D → _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ)
    (t : ∀ p, I → _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ),
    (∀ p, ∀ᶠ z in 𝓝 (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (n p)), DifferentiableAt ℂ (f p) z ∧
      DifferentiableAt ℂ (w0 p) z ∧
      (∀ k, DifferentiableAt ℂ (s p k) z) ∧ ∀ k, DifferentiableAt ℂ (t p k) z) →
    (∀ p, w0 p 0 ≠ 0 ∧ (∀ k, s p k 0 = 0) ∧
      (fderiv ℂ (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) 0).det
        ≠ 0) →
    (∀ v : J → ℂ, ∃ u : I → ℂ, ∀ p, ∑ k, u k * t p k 0 = v p) →
    ∃ cc : (Fin D → ℕ) → I → ℂ, ∀ p, (fun z => f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
      cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) =O[𝓝 0]
        fun z => ‖z‖ ^ a := by
  intro J I _ D T a haT n e f w0 s t hdiff hnz hsurj
  induction a with
  | zero =>
    refine ⟨0, fun p => ?_⟩
    have hf : ContinuousAt (f p) 0 := (hdiff p).self_of_nhds.1.continuousAt
    simpa using hf.tendsto.isBigO_one ℝ
  | succ a ih =>
    obtain ⟨cc, hcc⟩ := ih (by omega)
    have haT' : a ≤ T := by omega
    have hw0c : ∀ p, ContinuousAt (w0 p) 0 := fun p =>
      (hdiff p).self_of_nhds.2.1.continuousAt
    have hev : ∀ p, ∀ᶠ z in 𝓝 (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (n p)), (DifferentiableAt ℂ (f p) z ∧
        DifferentiableAt ℂ (w0 p) z ∧ (∀ k, DifferentiableAt ℂ (s p k) z) ∧
        ∀ k, DifferentiableAt ℂ (t p k) z) ∧ w0 p z ≠ 0 :=
      fun p => (hdiff p).and ((hw0c p).eventually_ne (hnz p).1)
    have htaylor : ∀ p, ∃ b : (Fin (n p) → ℕ) → ℂ, (fun z => (f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
        cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) -
        ∑ β ∈ Finset.Nat.antidiagonalTuple (n p) a, b β * ∏ k, (s p (e p k) z / w0 p z) ^ β k)
          =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
      intro p
      obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.mp (hev p)
      have hζ : DifferentiableOn ℂ
          (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) U := by
        intro z hz
        apply DifferentiableAt.differentiableWithinAt
        apply differentiableAt_euclidean.mpr
        intro k
        obtain ⟨⟨-, hw, hs, -⟩, hw0⟩ := hU z hz
        have hsk := hs (e p k)
        fun_prop (disch := assumption)
      have hg : DifferentiableOn ℂ (fun z => f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
          cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) U := by
        intro z hz
        apply DifferentiableAt.differentiableWithinAt
        obtain ⟨⟨hf, hw, hs, ht⟩, -⟩ := hU z hz
        fun_prop
      obtain ⟨b, hb⟩ := _root_.ReciprocityTheory.ChartRestriction.G.AR.taylor_expansion_local_coordinates (a := a) _
        (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) U 0 hUo h0U
        hg hζ (by simp [(hnz p).2.1]; rfl) (hnz p).2.2 (by simpa only [sub_zero] using hcc p)
      exact ⟨b, by simpa only [WithLp.ofLp_toLp, sub_zero] using hb⟩
    choose b hb using htaylor
    choose u hu using fun α : Fin D → ℕ => hsurj fun p => b p (α ∘ e p) / w0 p 0 ^ T
    refine ⟨fun α => if ∑ q, α q < a then cc α else u α, fun p => ?_⟩
    have hsplit : _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D (a + 1) = _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a ∪ Finset.Nat.antidiagonalTuple D a := by
      ext α
      simp only [Finset.mem_union, _root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff, Finset.Nat.mem_antidiagonalTuple]
      omega
    have hdisj : Disjoint (_root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a) (Finset.Nat.antidiagonalTuple D a) := by
      rw [Finset.disjoint_left]
      intro α h1 h2
      rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff] at h1
      rw [Finset.Nat.mem_antidiagonalTuple] at h2
      omega
    have hreidx : ∀ z, ∑ β ∈ Finset.Nat.antidiagonalTuple (n p) a,
        b p β * ∏ k, (s p (e p k) z / w0 p z) ^ β k =
        ∑ α ∈ Finset.Nat.antidiagonalTuple D a, b p (α ∘ e p) * ∏ q, (s p q z / w0 p z) ^ α q := by
      intro z
      symm
      refine Finset.sum_nbij' (fun α => α ∘ e p) (fun β => β ∘ (e p).symm) ?_ ?_ ?_ ?_ ?_
      · intro α hα
        simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
        rw [← hα]
        exact Equiv.sum_comp (e p) α
      · intro β hβ
        simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
        rw [← hβ]
        exact Equiv.sum_comp (e p).symm β
      · intro α _
        ext q
        simp
      · intro β _
        ext k
        simp
      · intro α _
        simp only [Function.comp_apply]
        rw [Equiv.prod_comp (e p) (fun q => (s p q z / w0 p z) ^ α q)]
    have hsum_split : ∀ z, ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D (a + 1), ∑ k,
        (if ∑ q, α q < a then cc α else u α) k * (∏ q, s p q z ^ α q) *
          w0 p z ^ (T - ∑ q, α q) * t p k z =
        ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
          cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z +
        ∑ α ∈ Finset.Nat.antidiagonalTuple D a, ∑ k,
          u α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z := by
      intro z
      rw [hsplit, Finset.sum_union hdisj]
      congr 1
      · refine Finset.sum_congr rfl fun α hα => ?_
        rw [if_pos (_root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff.mp hα)]
      · refine Finset.sum_congr rfl fun α hα => ?_
        rw [if_neg (by rw [Finset.Nat.mem_antidiagonalTuple.mp hα]; exact lt_irrefl a)]
    have hR : ∀ α ∈ Finset.Nat.antidiagonalTuple D a, (fun z => ∑ k, u α k *
        (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z -
        b p (α ∘ e p) * ∏ q, (s p q z / w0 p z) ^ α q) =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
      intro α hα
      have hsum : ∑ q, α q = a := Finset.Nat.mem_antidiagonalTuple.mp hα
      obtain ⟨-, hw, hs, ht⟩ := (hdiff p).self_of_nhds
      have hH0 : ∑ k, u α k * (w0 p 0 ^ T * t p k 0) = b p (α ∘ e p) := by
        have hw : w0 p 0 ^ T ≠ 0 := pow_ne_zero _ (hnz p).1
        have h : ∑ k, u α k * (w0 p 0 ^ T * t p k 0) = w0 p 0 ^ T * ∑ k, u α k * t p k 0 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [h, hu α p]
        field_simp
      have hHd : DifferentiableAt ℂ (fun z => ∑ k, u α k * (w0 p z ^ T * t p k z)) 0 := by
        fun_prop
      have hHO : (fun z => ∑ k, u α k * (w0 p z ^ T * t p k z) -
          ∑ k, u α k * (w0 p 0 ^ T * t p k 0)) =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p) => ‖z‖ := by
        simpa only [sub_zero] using hHd.hasFDerivAt.isBigO_sub.norm_right
      have hmono := _root_.GlobalTheory.JetsPure.monomial_isBigO (fun q z => s p q z / w0 p z)
        (fun q => by
          have hsq := hs q
          have hw00 := (hnz p).1
          fun_prop (disch := assumption)) (fun q => by simp [(hnz p).2.1]) α
      rw [hsum] at hmono
      refine (hmono.mul hHO).congr' ?_ (Eventually.of_forall fun z => by ring)
      filter_upwards [(hw0c p).eventually_ne (hnz p).1] with z hz
      rw [hH0]
      have hP : ∏ q, s p q z ^ α q = (∏ q, (s p q z / w0 p z) ^ α q) * w0 p z ^ a := by
        rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hz)]
      have hW : w0 p z ^ a * w0 p z ^ (T - a) = w0 p z ^ T := by
        rw [← pow_add, Nat.add_sub_cancel' haT']
      rw [hsum, hP, mul_sub, Finset.mul_sum, ← hW]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · ring
    refine ((hb p).sub (IsBigO.sum hR)).congr' (Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => rfl)
    clear hdiff hnz hsurj ih hcc hev hsplit hdisj hR hw0c hb hu
    beta_reduce
    rw [hsum_split z, hreidx z, Finset.sum_apply, Finset.sum_sub_distrib]
    ring
end _root_.GlobalTheory.JetsPure
end GlobalTheory.JetsPure
