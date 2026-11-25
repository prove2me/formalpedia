-- Prove2me | solution 1 for GlobalTheory.idealCharacter_LSeries_continuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:00:32.805231+00:00
-- url     : https://prove2.me/submissions/8a8dfe13-993c-4d7a-83fb-675a03755b64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SmoothedIdealCharacterSumMainTermIdealClassRepre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEntireMellinSmoothedDirichletSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLSeriesContinuation
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_SmoothedSumMellin_exists_entire_mellin
import Theorems.Thm_GlobalTheory_countable_ideal_and_summable_absNorm_rpow
import Theorems.Thm_GlobalTheory_exists_integral_ideal_in_class_coprime
import Theorems.Thm_GlobalTheory_smoothedSum_main_term_representatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
open Filter Topology Set Asymptotics in
private theorem eq_of_norm_sub_div_le {f : ℝ → ℂ} {R R' : ℂ} {C C' : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖f t - R / t‖ ≤ C)
    (h' : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖f t - R' / t‖ ≤ C') : R = R' := by
  by_contra hne
  have hd : 0 < ‖R - R'‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set D := |C| + |C'| + 1 with hD_def
  have hD : 0 < D := by positivity
  set t := min 1 (‖R - R'‖ / (2 * D)) with ht_def
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htD : t * D ≤ ‖R - R'‖ / 2 := by
    calc t * D ≤ ‖R - R'‖ / (2 * D) * D := by gcongr; exact min_le_right _ _
      _ = ‖R - R'‖ / 2 := by field_simp
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
  have key : R - R' = (t : ℂ) * ((f t - R' / t) - (f t - R / t)) := by
    field_simp
    ring
  have hle : ‖R - R'‖ ≤ t * (C' + C) := by
    rw [key, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add (h' t ht0 ht1) (h t ht0 ht1))
  have : t * (C' + C) ≤ t * D :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self C, le_abs_self C']) ht0.le
  linarith
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
open Filter Topology Set Asymptotics in
private theorem exists_differentiable_eq_div_of_family {ι : Type} (M G : ι → ℂ → ℂ)
    (F : ℂ → ℂ) (hM : ∀ i, Differentiable ℂ (M i)) (hG : ∀ i, Differentiable ℂ (G i))
    (hGF : ∀ i s, 1 < s.re → G i s = M i s * F s) (hne : ∀ s, ∃ i, M i s ≠ 0) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s, 1 < s.re → Z s = F s) ∧
      ∀ i s, M i s ≠ 0 → Z s = G i s / M i s := by
  have hcross : ∀ i j s, G i s * M j s = G j s * M i s := by
    intro i j s
    have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (fun s => G i s * M j s) =ᶠ[𝓝 (2 : ℂ)] fun s => G j s * M i s := by
      filter_upwards [hU.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
      rw [hGF i s hs, hGF j s hs]
      ring
    have hf : AnalyticOnNhd ℂ (fun s => G i s * M j s) univ :=
      fun z _ => ((hG i).mul (hM j)).analyticAt z
    have hg : AnalyticOnNhd ℂ (fun s => G j s * M i s) univ :=
      fun z _ => ((hG j).mul (hM i)).analyticAt z
    exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ _) h2
      (mem_univ s)
  choose w hw using hne
  have hZ : ∀ i s, M i s ≠ 0 → G (w s) s / M (w s) s = G i s / M i s := by
    intro i s hi
    rw [div_eq_div_iff (hw s) hi]
    exact hcross (w s) i s
  refine ⟨fun s => G (w s) s / M (w s) s, ?_, ?_, hZ⟩
  · intro s₀
    have hev : ∀ᶠ s in 𝓝 s₀, M (w s₀) s ≠ 0 :=
      (hM (w s₀)).continuous.continuousAt.eventually_ne (hw s₀)
    exact (((hG _) s₀).div ((hM _) s₀) (hw s₀)).congr_of_eventuallyEq
      (hev.mono fun s hs => hZ _ s hs)
  · intro s hs
    simp only
    rw [hGF _ s hs, mul_div_cancel_left₀ _ (hw s)]
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
open Filter Topology Set Asymptotics in
private theorem differentiable_mellin_of_support_in_Icc_pos {w : ℝ → ℂ} (hw : Continuous w) {a b : ℝ}
    (ha : 0 < a) (hab : ∀ y, w y ≠ 0 → a ≤ y ∧ y ≤ b) : Differentiable ℂ (mellin w) := by
  intro s
  have htop : w =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra h
    exact absurd (hab y h).2 (not_le.2 hy)
  have hzero : w =ᶠ[𝓝[>] 0] 0 := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra h
    exact absurd (hab y h).1 (not_le.2 hy.2)
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (hw.locallyIntegrable.locallyIntegrableOn _)
    ((isBigO_zero _ _).congr' htop.symm EventuallyEq.rfl) (by linarith)
    ((isBigO_zero _ _).congr' hzero.symm EventuallyEq.rfl) (by linarith)
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
open Filter Topology Set Asymptotics in
private theorem exists_weight_mellin_ne_zero (s₀ : ℂ) :
    ∃ w : ℝ → ℂ, ContDiff ℝ ∞ w ∧ (∃ a b : ℝ, 0 < a ∧ ∀ y, w y ≠ 0 → a ≤ y ∧ y ≤ b) ∧
      mellin w s₀ ≠ 0 := by
  let ψ : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hψ0 : ∀ y : ℝ, y ≤ 0 → ψ y = 0 := fun y hy => ψ.zero_of_le_dist (by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    show (1 : ℝ) ≤ _
    linarith)
  refine ⟨fun y => Complex.exp (-(s₀ - 1) * (Real.log y : ℂ)) * (ψ y : ℂ), ?_,
    ⟨1, 3, one_pos, ?_⟩, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport ψ
    · have hx0 : x ≠ 0 := by
        rintro rfl
        rw [ψ.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hx
        norm_num at hx
      have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => Complex.exp (-(s₀ - 1) * (Real.log y : ℂ))) x :=
        Complex.contDiff_exp.contDiffAt.comp x (contDiffAt_const.mul
          (ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.2 hx0)))
      exact h1.mul (ofRealCLM.contDiff.comp ψ.contDiff).contDiffAt
    · have hev : (fun y => Complex.exp (-(s₀ - 1) * (Real.log y : ℂ)) * (ψ y : ℂ)) =ᶠ[𝓝 x]
          fun _ => 0 :=
        (notMem_tsupport_iff_eventuallyEq.1 hx).mono fun y hy => by simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro y hy
    have hψy : ψ y ≠ 0 := fun h => hy (by simp [h])
    have hmem : y ∈ Metric.ball (2 : ℝ) 1 := by
      rw [← ψ.support_eq]
      exact hψy
    rw [Real.ball_eq_Ioo] at hmem
    constructor <;> linarith [hmem.1, hmem.2]
  · have hint : ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s₀ - 1) •
        (Complex.exp (-(s₀ - 1) * (Real.log y : ℂ)) * (ψ y : ℂ)) =
        ∫ y in Ioi (0 : ℝ), ((ψ y : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      simp only [smul_eq_mul]
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.2 (ne_of_gt hy)),
        ← Complex.ofReal_log (le_of_lt hy), ← mul_assoc, ← Complex.exp_add,
        show (Real.log y : ℂ) * (s₀ - 1) + -(s₀ - 1) * (Real.log y : ℂ) = 0 by ring,
        Complex.exp_zero, one_mul]
    unfold mellin
    rw [hint, integral_complex_ofReal, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y (hy : y ∉ Ioi (0 : ℝ)) => hψ0 y (not_lt.1 hy))]
    exact ofReal_ne_zero.2 ψ.integral_pos.ne'
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open Filter Topology Set Asymptotics
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (φ : mixedSpace K → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ I J, X (I * J) = X I * X J) → (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) → (∀ I, I ⊔ m ≠ ⊤ → X I = 0) → (∀ x y, φ (x * y) = φ x * φ y) → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) → ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} → (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ∧ ((∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → Z 1 = 0) := by
  intro K _ _ m X φ hm hX0 hXmul hXn hXz hφmul hφh hφs hφn hβ
  have hmain := _root_.GlobalTheory.smoothedSum_main_term_representatives K m X φ hm hX0 hXmul
    hXn hXz hφmul hφh hφs hφn hβ
  obtain ⟨hcount, hsum⟩ := _root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K
  haveI := hcount
  choose b hb using _root_.GlobalTheory.exists_integral_ideal_in_class_coprime K m hm
  have hbij : Function.Bijective fun c => ClassGroup.mk0 (b c) := by
    have : (fun c => ClassGroup.mk0 (b c)) = id := funext fun c => (hb c).1
    rw [this]
    exact Function.bijective_id
  have hbm : ∀ c, (b c : Ideal (𝓞 K)) ⊔ m = ⊤ := fun c => (hb c).2
  have hXle : ∀ I, ‖X I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · rw [hI, hX0, norm_zero]
      exact zero_le_one
    by_cases hIm : I ⊔ m = ⊤
    · rw [hXn I hI hIm]
    · rw [hXz I hIm, norm_zero]
      exact zero_le_one
  have hN : ∀ I, X I ≠ 0 → (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
    intro I hI
    have hI0 : I ≠ ⊥ := fun h => hI (h ▸ hX0)
    have : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hsumm : ∀ σ : ℝ, 1 < σ → Summable fun I => ‖X I‖ * (Ideal.absNorm I : ℝ) ^ (-σ) := by
    intro σ hσ
    refine ((hsum σ hσ).1).of_nonneg_of_le
      (fun I => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) fun I => ?_
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hXle I)
  set S := ∑ c, (X (b c : Ideal (𝓞 K)))⁻¹ with hS
  set F : ℂ → ℂ := fun s => (s - 1) * ∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) with hF
  have hweight : ∀ w : {w : ℝ → ℂ // ContDiff ℝ ∞ w ∧
      ∃ a b : ℝ, 0 < a ∧ ∀ y, w y ≠ 0 → a ≤ y ∧ y ≤ b},
      ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ s, 1 < s.re → G s = mellin w.1 s * F s) ∧
        ((∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → G 1 = 0) := by
    rintro ⟨w, hw, hwsupp⟩
    obtain ⟨κ, hκ⟩ := hmain w hw hwsupp
    obtain ⟨G, hGd, hG1, hGs⟩ := _root_.GlobalTheory.SmoothedSumMellin.exists_entire_mellin (Ideal (𝓞 K)) X
      (fun I => (Ideal.absNorm I : ℝ)) (κ * S) w hw hwsupp hN hsumm (hκ b hbij hbm)
    refine ⟨G, hGd, fun s hs => ?_, fun hJ => ?_⟩
    · rw [hGs s hs]
      simp only [F, Complex.ofReal_natCast]
    · rw [hG1]
      obtain ⟨J, hJ0, hJm, hXJ⟩ := hJ
      let J' : (Ideal (𝓞 K))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩
      let b' : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰ :=
        fun c => b (c * (ClassGroup.mk0 J')⁻¹) * J'
      have hb'mk : ∀ c, ClassGroup.mk0 (b' c) = c := by
        intro c
        simp only [b', map_mul, (hb _).1, inv_mul_cancel_right]
      have hbij' : Function.Bijective fun c => ClassGroup.mk0 (b' c) := by
        have : (fun c => ClassGroup.mk0 (b' c)) = id := funext hb'mk
        rw [this]
        exact Function.bijective_id
      have hbm' : ∀ c, (b' c : Ideal (𝓞 K)) ⊔ m = ⊤ := by
        intro c
        simp only [b', Submonoid.coe_mul]
        rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rw [sup_comm]; exact hbm _), sup_comm]
        exact hJm
      have hS' : ∑ c, (X (b' c : Ideal (𝓞 K)))⁻¹ = (X J)⁻¹ * S := by
        simp only [b', Submonoid.coe_mul, hXmul, mul_inv, hS, Finset.mul_sum]
        exact Fintype.sum_equiv (Equiv.mulRight (ClassGroup.mk0 J')⁻¹) _ _ fun c => by
          simp only [Equiv.coe_mulRight]
          ring
      have heq : κ * S = κ * ((X J)⁻¹ * S) := by
        obtain ⟨C, hC⟩ := hκ b hbij hbm 0
        obtain ⟨C', hC'⟩ := hκ b' hbij' hbm' 0
        rw [← hS']
        refine eq_of_norm_sub_div_le (f := fun t => ∑' I, X I * w (t * (Ideal.absNorm I : ℝ))) (C := C) (C' := C') (fun t h0 h1 => ?_) (fun t h0 h1 => ?_)
        · have := hC t h0 h1
          rwa [pow_zero, mul_one] at this
        · have := hC' t h0 h1
          rwa [pow_zero, mul_one] at this
      have hinv : (X J)⁻¹ ≠ 1 := fun h => hXJ (inv_eq_one.1 h)
      have h0 : κ * S * (1 - (X J)⁻¹) = 0 := by linear_combination heq
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h).symm hinv
  choose G hGd hGF hG1 using hweight
  obtain ⟨Z, hZd, hZF, hZdiv⟩ := exists_differentiable_eq_div_of_family (fun w => mellin w.1) G F
    (fun w => by
      obtain ⟨a, c, ha, hac⟩ := w.2.2
      exact differentiable_mellin_of_support_in_Icc_pos w.2.1.continuous ha hac)
    hGd hGF (fun s => by
      obtain ⟨w, hw, hws, hne⟩ := exists_weight_mellin_ne_zero s
      exact ⟨⟨w, hw, hws⟩, hne⟩)
  refine ⟨Z, hZd, hZF, fun hJ => ?_⟩
  obtain ⟨w, hw, hws, hne⟩ := exists_weight_mellin_ne_zero 1
  rw [hZdiv ⟨w, hw, hws⟩ 1 hne, hG1 _ hJ, zero_div]
end _root_.GlobalTheory
end GlobalTheory
