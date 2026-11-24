-- Prove2me | solution 1 for GlobalTheory.LatExpSum.summable_exp_neg_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:35.25764+00:00
-- url     : https://prove2.me/submissions/d97835ea-42ef-4199-9866-f57ab72863a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableExpNegTraceTotallyPositiveFractionalIdea
import Theorems.Thm_GlobalTheory_LatExpSum_trace_eq_sum_emb
import Theorems.Thm_GlobalTheory_LatExpSum_summable_pi_prod
import Theorems.Thm_GlobalTheory_LatExpSum_summable_exp_neg_abs
import Theorems.Thm_GlobalTheory_LatExpSum_repr_eq_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
noncomputable section
open GlobalTheory GlobalTheory.LatExpSum
namespace GlobalTheory.LatExpSum
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) (δ : ℝ), 0 < δ → Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
  intro F _ _ _ L δ hδ
  classical
  obtain ⟨a, ha, hint⟩ := L.isFractional
  have hz : ∀ x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x}, ∃ w : 𝓞 F,
      algebraMap (𝓞 F) F w = algebraMap (𝓞 F) F a * x.1 := fun x => by
    obtain ⟨w, hw⟩ := hint x.1 x.2.1
    exact ⟨w, by rw [hw, Algebra.smul_def]⟩
  choose z hz using hz
  let b := integralBasis F
  let d := (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b
  have hrepr : ∀ (y : F) i, b.repr y i = Algebra.trace ℚ F (d i * y) := fun y i => repr_eq_trace F b y i
  let c : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ :=
    fun x => (RingOfIntegers.basis F).repr (z x)
  have hc : ∀ x i, ((c x i : ℚ)) = Algebra.trace ℚ F ((d i * algebraMap (𝓞 F) F a) * x.1) := by
    intro x i
    have := integralBasis_repr_apply (K := F) (z x) i
    rw [hz x] at this
    rw [mul_assoc, ← hrepr]
    rw [this, eq_intCast]
  let Mi : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ := fun i => ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)|
  have hMi : ∀ i, 0 ≤ Mi i := fun i => Finset.sum_nonneg fun τ _ => abs_nonneg _
  let M : ℝ := ∑ i, Mi i + 1
  have hM : 0 < M := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hMi i
    show 0 < ∑ i, Mi i + 1
    linarith
  have hbound : ∀ x, ∑ i, |(c x i : ℝ)| ≤ M * ∑ τ : Emb F, τ x.1 := by
    intro x
    have hT : 0 ≤ ∑ τ : Emb F, τ x.1 := Finset.sum_nonneg fun τ _ => (x.2.2 τ).le
    have h1 : ∀ i, |(c x i : ℝ)| ≤ Mi i * ∑ τ : Emb F, τ x.1 := by
      intro i
      have e : (c x i : ℝ) = ∑ τ : Emb F, τ (d i * algebraMap (𝓞 F) F a) * τ x.1 := by
        have h := congrArg (fun q : ℚ => (q : ℝ)) (hc x i)
        simp only [Rat.cast_intCast] at h
        rw [h, trace_eq_sum_emb]
        simp only [map_mul]
      rw [e]
      calc |∑ τ : Emb F, τ (d i * algebraMap (𝓞 F) F a) * τ x.1|
          ≤ ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a) * τ x.1| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)| * τ x.1 := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [abs_mul, abs_of_pos (x.2.2 τ)]
        _ ≤ ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)| * ∑ σ : Emb F, σ x.1 :=
          Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun σ : Emb F => σ x.1) (fun σ _ => (x.2.2 σ).le) (Finset.mem_univ τ)) (abs_nonneg _)
        _ = Mi i * ∑ τ : Emb F, τ x.1 := by rw [Finset.sum_mul]
    calc ∑ i, |(c x i : ℝ)| ≤ ∑ i, Mi i * ∑ τ : Emb F, τ x.1 := Finset.sum_le_sum fun i _ => h1 i
      _ = (∑ i, Mi i) * ∑ τ : Emb F, τ x.1 := by rw [Finset.sum_mul]
      _ ≤ M * ∑ τ : Emb F, τ x.1 := mul_le_mul_of_nonneg_right (by simp [M]) hT
  have ha0 : algebraMap (𝓞 F) F a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero ha)
  have hinj : Function.Injective c := by
    intro x y hxy
    have h1 : z x = z y := (RingOfIntegers.basis F).repr.injective (Finsupp.ext fun i => congrFun hxy i)
    have h2 : algebraMap (𝓞 F) F a * x.1 = algebraMap (𝓞 F) F a * y.1 := by rw [← hz, ← hz, h1]
    exact Subtype.ext (mul_left_cancel₀ ha0 h2)
  have hε : 0 < δ / M := div_pos hδ hM
  have hg : Summable fun n : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ => ∏ i, Real.exp (-(δ / M) * |(n i : ℝ)|) :=
    summable_pi_prod (f := fun _ x => Real.exp (-(δ / M) * |(x : ℝ)|)) (fun _ _ => (Real.exp_pos _).le) fun _ => summable_exp_neg_abs hε
  refine (hg.comp_injective hinj).of_nonneg_of_le (fun _ => (Real.exp_pos _).le) fun x => ?_
  simp only [Function.comp_apply]
  rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
  have h3 : δ / M * ∑ i, |(c x i : ℝ)| ≤ δ * ∑ τ : Emb F, τ x.1 := by
    calc δ / M * ∑ i, |(c x i : ℝ)| ≤ δ / M * (M * ∑ τ : Emb F, τ x.1) := mul_le_mul_of_nonneg_left (hbound x) hε.le
      _ = δ * ∑ τ : Emb F, τ x.1 := by field_simp
  linarith
end GlobalTheory.LatExpSum
