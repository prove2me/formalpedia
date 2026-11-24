-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SchwartzBaire.exists_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:56:15.205798+00:00
-- url     : https://prove2.me/submissions/4332facd-6a15-45b3-867f-9981f641a5e2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SchwartzBaire_iteratedFDeriv_sub_apply__4bfc50ada7a9
import Theorems.Thm_GlobalTheory_CompanionTheory_SchwartzBaire_cauchy_weighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff Topology Uniformity
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchwartzBaire
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory.CompanionTheory.SchwartzBaire
theorem _root_.solution [CompleteSpace F] (f : ℕ → 𝓢(E, F)) (hf : CauchySeq f) :
    ∃ g : 𝓢(E, F), Tendsto f atTop (𝓝 g) := by
  have hpt : ∀ l x, CauchySeq (fun n => iteratedFDeriv ℝ l (f n) x) := by
    intro l x
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := cauchy_weighted f hf 0 l (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn N le_rfl x
    rw [pow_zero, one_mul] at h
    rw [dist_eq_norm]
    linarith
  choose G hG using fun l x => cauchySeq_tendsto_of_complete (hpt l x)
  have hlim : ∀ k l {δ : ℝ}, 0 < δ → ∃ N, ∀ m ≥ N, ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - G l x‖ ≤ δ := by
    intro k l δ hδ
    obtain ⟨N, hN⟩ := cauchy_weighted f hf k l hδ
    refine ⟨N, fun m hm x => ?_⟩
    have ht : Tendsto (fun m' => ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - iteratedFDeriv ℝ l (f m') x‖)
        atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - G l x‖)) :=
      ((tendsto_const_nhds.sub (hG l x)).norm).const_mul _
    exact le_of_tendsto ht (eventually_atTop.2 ⟨N, fun m' hm' => hN m hm m' hm' x⟩)
  have hunif : ∀ l, TendstoUniformly (fun n x => iteratedFDeriv ℝ l (f n) x) (G l) atTop := by
    intro l
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hlim 0 l (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with n hn x
    have h := hN n hn x
    rw [pow_zero, one_mul] at h
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  let g₀ : E → F := fun x => (G 0 x).curry0
  let p : E → FormalMultilinearSeries ℝ E F := fun x l => G l x
  have hT : HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) g₀ p := by
    refine ⟨fun x => rfl, fun m _ x => ?_, fun m _ => ?_⟩
    · have hU : TendstoUniformly (fun n y => (iteratedFDeriv ℝ (m + 1) (f n) y).curryLeft)
          (fun y => (G (m + 1) y).curryLeft) atTop :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).isometry.uniformContinuous.comp_tendstoUniformly
          (hunif (m + 1))
      exact hasFDerivAt_of_tendstoUniformly (f := fun n y => iteratedFDeriv ℝ m (f n) y) hU
        (fun n y => ((f n).smooth ⊤).ftaylorSeries.fderiv m (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top m)) y)
        (fun y => hG m y) x
    · exact (hunif m).continuous (Frequently.of_forall fun n => ((f n).smooth m).continuous_iteratedFDeriv le_rfl)
  have hg : ∀ l x, iteratedFDeriv ℝ l g₀ x = G l x := fun l x =>
    (hT.eq_iteratedFDeriv (WithTop.coe_le_coe.2 le_top) x).symm
  have hdecay : ∀ k l : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ l g₀ x‖ ≤ C := by
    intro k l
    obtain ⟨N, hN⟩ := hlim k l one_pos
    refine ⟨1 + SchwartzMap.seminorm ℝ k l (f N), fun x => ?_⟩
    rw [hg]
    have h1 := hN N le_rfl x
    have h2 := SchwartzMap.le_seminorm ℝ k l (f N) x
    have h3 : ‖G l x‖ ≤ ‖iteratedFDeriv ℝ l (f N) x‖ + ‖iteratedFDeriv ℝ l (f N) x - G l x‖ := by
      calc ‖G l x‖ = ‖iteratedFDeriv ℝ l (f N) x - (iteratedFDeriv ℝ l (f N) x - G l x)‖ := by
            rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have hxk : 0 ≤ ‖x‖ ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hxk]
  let g : 𝓢(E, F) := ⟨g₀, hT.contDiff, hdecay⟩
  have hcoe : (⇑g : E → F) = g₀ := rfl
  refine ⟨g, ?_⟩
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds _ _]
  intro i ε hε
  obtain ⟨N, hN⟩ := hlim i.1 i.2 (half_pos hε)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hb : SchwartzMap.seminorm ℝ i.1 i.2 (f m - g) ≤ ε / 2 :=
    SchwartzMap.seminorm_le_bound ℝ i.1 i.2 _ (by positivity) fun x => by
      rw [iteratedFDeriv_sub_apply', hcoe, hg]
      exact hN m hm x
  exact lt_of_le_of_lt hb (half_lt_self hε)
end GlobalTheory.CompanionTheory.SchwartzBaire
