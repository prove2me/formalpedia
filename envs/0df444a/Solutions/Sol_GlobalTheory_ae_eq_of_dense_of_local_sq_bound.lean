-- Prove2me | solution 1 for GlobalTheory.ae_eq_of_dense_of_local_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:23.737977+00:00
-- url     : https://prove2.me/submissions/08ff4cf6-5615-4f1a-b4cf-774917ee4b2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AeEqOfDenseOfLocalSqBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Set H), Dense D → ∀ P Q : H → X → E,
    (∀ u u', (fun x => P u x - P u' x) =ᵐ[μ] P (u - u')) →
    (∀ u u', (fun x => Q u x - Q u' x) =ᵐ[μ] Q (u - u')) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (P u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖P u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (Q u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖Q u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ u ∈ D, P u =ᵐ[μ] Q u) → ∀ u, P u =ᵐ[μ] Q u := by
  intro X _ μ K _hK hcov H _ _ E _ _ D hD P Q hP hQ hPb hQb hPQ u
  have key : ∀ n, ∀ᵐ x ∂μ.restrict (K n), P u x = Q u x := by
    intro n
    obtain ⟨CP, hCP⟩ := hPb n
    obtain ⟨CQ, hCQ⟩ := hQb n
    have hmeas : AEMeasurable (fun x => ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2) (μ.restrict (K n)) :=
      (((hCP u).1.sub (hCQ u).1).nnnorm.aemeasurable.coe_nnreal_ennreal).pow_const 2
    set M : ℝ := 2 * (|CP| + |CQ|) with hM
    have hbound : ∀ δ : ℝ, 0 < δ →
        ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) ≤ ENNReal.ofReal (M * δ ^ 2) := by
      intro δ hδ
      obtain ⟨u', hu'D, hdist⟩ := hD.exists_dist_lt u hδ
      have hwδ : ‖u - u'‖ ^ 2 ≤ δ ^ 2 := by
        have : ‖u - u'‖ < δ := by rw [← dist_eq_norm]; exact hdist
        exact pow_le_pow_left₀ (norm_nonneg _) this.le 2
      have hae : ∀ᵐ x ∂(μ.restrict (K n)), ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ≤
          2 * ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2 := by
        have h1 := ae_restrict_of_ae (s := K n) (hP u u')
        have h2 := ae_restrict_of_ae (s := K n) (hQ u u')
        have h3 := ae_restrict_of_ae (s := K n) (hPQ u' hu'D)
        filter_upwards [h1, h2, h3] with x e1 e2 e3
        have e1' : P u x - P u' x = P (u - u') x := e1
        have e2' : Q u x - Q u' x = Q (u - u') x := e2
        have e3' : P u' x = Q u' x := e3
        have e : P u x - Q u x = P (u - u') x - Q (u - u') x := by
          have : P u x - Q u x = (P u x - P u' x) - (Q u x - Q u' x) + (P u' x - Q u' x) := by abel
          rw [this, e1', e2', e3', sub_self, add_zero]
        rw [e]
        have hn : ‖P (u - u') x - Q (u - u') x‖₊ ≤ ‖P (u - u') x‖₊ + ‖Q (u - u') x‖₊ := nnnorm_sub_le _ _
        have hsq : ‖P (u - u') x - Q (u - u') x‖₊ ^ 2 ≤
            2 * ‖P (u - u') x‖₊ ^ 2 + 2 * ‖Q (u - u') x‖₊ ^ 2 := by
          have hn' : ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) ≤
              ((‖P (u - u') x‖₊ : NNReal) : ℝ) + ((‖Q (u - u') x‖₊ : NNReal) : ℝ) := by exact_mod_cast hn
          have h0 : (0:ℝ) ≤ ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) := NNReal.coe_nonneg _
          have hreal : ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) ^ 2 ≤
              2 * ((‖P (u - u') x‖₊ : NNReal) : ℝ) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : NNReal) : ℝ) ^ 2 := by
            nlinarith [sq_nonneg (((‖P (u - u') x‖₊ : NNReal) : ℝ) - ((‖Q (u - u') x‖₊ : NNReal) : ℝ))]
          exact_mod_cast hreal
        have := ENNReal.coe_le_coe.mpr hsq
        push_cast at this
        exact this
      calc ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n))
          ≤ ∫⁻ x, (2 * ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2)
              ∂(μ.restrict (K n)) := lintegral_mono_ae hae
        _ = 2 * ∫⁻ x, ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) +
              2 * ∫⁻ x, ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) := by
            rw [lintegral_add_left'
              (((hCP (u - u')).1.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2).const_mul 2),
              lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * ENNReal.ofReal (CP * ‖u - u'‖ ^ 2) + 2 * ENNReal.ofReal (CQ * ‖u - u'‖ ^ 2) := by
            gcongr
            · exact (hCP (u - u')).2
            · exact (hCQ (u - u')).2
        _ ≤ 2 * ENNReal.ofReal (|CP| * δ ^ 2) + 2 * ENNReal.ofReal (|CQ| * δ ^ 2) := by
            gcongr <;> first | exact le_abs_self _ | exact hwδ
        _ = ENNReal.ofReal (M * δ ^ 2) := by
            have : M * δ ^ 2 = 2 * (|CP| * δ ^ 2) + 2 * (|CQ| * δ ^ 2) := by rw [hM]; ring
            rw [this, ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
            simp
    have hzero : ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) = 0 := by
      have hlim : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (M * δ ^ 2)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (ENNReal.ofReal (M * 0 ^ 2))) := by
        apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
        exact (ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow 2))).tendsto 0
      have := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall (fun δ hδ => hbound δ hδ))
      simpa using this
    have hae0 := (lintegral_eq_zero_iff' hmeas).mp hzero
    filter_upwards [hae0] with x hx
    have hx' : ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 = 0 := hx
    simpa [sub_eq_zero] using hx'
  have hall : ∀ᵐ x ∂μ.restrict (⋃ n, K n), P u x = Q u x :=
    (ae_restrict_iUnion_iff K (fun x => P u x = Q u x)).mpr key
  rw [hcov, Measure.restrict_univ] at hall
  exact hall
end GlobalTheory
