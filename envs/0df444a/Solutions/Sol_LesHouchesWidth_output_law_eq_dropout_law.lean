-- Prove2me | solution 1 for LesHouchesWidth.output_law_eq_dropout_law
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T14:07:17.581798+00:00
-- url     : https://prove2.me/submissions/f5b28877-e340-4750-b47c-a8d29811abc7

import Mathlib
import Definitions.Def_LesHouchesWidth_ReLUNet

set_option autoImplicit false

namespace P54dae77a

open MeasureTheory LesHouchesWidth

/-- Sign of hidden neuron `i` of layer `ℓ + 1` (and `1` outside the hidden layers). -/
noncomputable def sgnV {n : ℕ → ℕ} {L : ℕ} (ε : MaskIndex n L → Bool) (ℓ : ℕ)
    (i : Fin (n (ℓ + 1))) : ℝ :=
  if h : ℓ < L then (if ε ⟨⟨ℓ, h⟩, i⟩ then 1 else -1) else 1

/-- Sign of neuron `i` of layer `ℓ` (input layer: `1`). -/
noncomputable def sgnL {n : ℕ → ℕ} {L : ℕ} (ε : MaskIndex n L → Bool) :
    (ℓ : ℕ) → Fin (n ℓ) → ℝ
  | 0, _ => 1
  | ℓ + 1, i => sgnV ε ℓ i

noncomputable def coef {n : ℕ → ℕ} {L : ℕ} (ε : MaskIndex n L → Bool) (k : WeightIndex n L) :
    ℝ :=
  sgnV ε k.1.val k.2.1 * sgnL ε k.1.val k.2.2

/-- Flip the sign of every weight entering / leaving each hidden neuron with `ε = false`. -/
noncomputable def flipW {n : ℕ → ℕ} {L : ℕ} (ε : MaskIndex n L → Bool) (ω : Weights n L) :
    Weights n L :=
  fun k => coef ε k * ω k

/-- The one-sided activation `p ↦ p 1{p ≥ 0}` (`b = true`) or `p ↦ p 1{p < 0}` (`b = false`). -/
noncomputable def actS (b : Bool) (p : ℝ) : ℝ :=
  if b then (if 0 ≤ p then p else 0) else (if p < 0 then p else 0)

/-- Hidden states of the network with one-sided activations chosen by `ε`. -/
noncomputable def sh {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (ε : MaskIndex n L → Bool)
    (x : Fin (n 0) → ℝ) : (ℓ : ℕ) → Fin (n ℓ) → ℝ
  | 0 => x
  | ℓ + 1 => fun i =>
      if h : ℓ < L then actS (ε ⟨⟨ℓ, h⟩, i⟩) (∑ j, weight ω ℓ i j * sh ω ε x ℓ j)
      else ∑ j, weight ω ℓ i j * sh ω ε x ℓ j

noncomputable def pre {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (ε : MaskIndex n L → Bool)
    (x : Fin (n 0) → ℝ) (ℓ : ℕ) (i : Fin (n (ℓ + 1))) : ℝ :=
  ∑ j, weight ω ℓ i j * sh ω ε x ℓ j

noncomputable def bitf (b : Bool) (p : ℝ) : Bool :=
  if b then decide (0 ≤ p) else decide (p < 0)

/-- The data-dependent mask produced by the sign pattern `ε`. -/
noncomputable def mk {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (ε : MaskIndex n L → Bool)
    (x : Fin (n 0) → ℝ) : MaskIndex n L → Bool :=
  fun k => bitf (ε k) (pre ω ε x k.1.val k.2)

theorem maskValue_bitf (b : Bool) (p : ℝ) :
    (if bitf b p then (1 : ℝ) else 0) * p = actS b p := by
  cases b <;> rcases le_or_gt 0 p with hp | hp <;>
    simp [bitf, actS, hp, not_lt.mpr, not_le.mpr]

theorem bitf_inj {b b' : Bool} {p : ℝ} (h : bitf b p = bitf b' p) : b = b' := by
  cases b <;> cases b' <;> simp only [bitf] at h ⊢ <;>
    rcases le_or_gt 0 p with hp | hp <;> simp_all [not_lt.mpr, not_le.mpr]

theorem sign_relu (b : Bool) (p : ℝ) :
    (if b then (1 : ℝ) else -1) * relu ((if b then (1 : ℝ) else -1) * p) = actS b p := by
  unfold relu actS
  cases b <;> rcases le_or_gt 0 p with hp | hp
  · simp only [Bool.false_eq_true, if_false, if_neg (not_lt.mpr hp)]
    rw [max_eq_right (by linarith)]; ring
  · simp only [Bool.false_eq_true, if_false, if_pos hp]
    rw [max_eq_left (by linarith)]; ring
  · simp only [if_true, if_pos hp]
    rw [max_eq_left (by linarith)]; ring
  · simp only [if_true, if_neg (not_le.mpr hp)]
    rw [max_eq_right (by linarith)]; ring

theorem dropout_eq_sh {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (ε : MaskIndex n L → Bool)
    (x : Fin (n 0) → ℝ) : ∀ ℓ, dropoutHidden ω (mk ω ε x) x ℓ = sh ω ε x ℓ := by
  intro ℓ
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    funext i
    show maskValue (mk ω ε x) ℓ i * ∑ j, weight ω ℓ i j * dropoutHidden ω (mk ω ε x) x ℓ j =
      sh ω ε x (ℓ + 1) i
    rw [ih]
    unfold maskValue
    by_cases h : ℓ < L
    · rw [dif_pos h]
      simp only [sh, dif_pos h]
      exact maskValue_bitf _ _
    · rw [dif_neg h]
      simp only [sh, dif_neg h]
      ring

theorem weight_flip {n : ℕ → ℕ} {L : ℕ} (ε : MaskIndex n L → Bool) (ω : Weights n L) (ℓ : ℕ)
    (i : Fin (n (ℓ + 1))) (j : Fin (n ℓ)) :
    weight (flipW ε ω) ℓ i j = sgnV ε ℓ i * sgnL ε ℓ j * weight ω ℓ i j := by
  unfold weight
  split_ifs with h
  · show Real.sqrt (2 / (n ℓ : ℝ)) * (sgnV ε ℓ i * sgnL ε ℓ j * ω ⟨⟨ℓ, h⟩, (i, j)⟩) =
      sgnV ε ℓ i * sgnL ε ℓ j * (Real.sqrt (2 / (n ℓ : ℝ)) * ω ⟨⟨ℓ, h⟩, (i, j)⟩)
    ring
  · ring

theorem netZ_flip {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (ε : MaskIndex n L → Bool)
    (x : Fin (n 0) → ℝ) :
    ∀ ℓ, ℓ ≤ L → ∀ i : Fin (n (ℓ + 1)),
      netZ (flipW ε ω) x (ℓ + 1) i = sgnV ε ℓ i * pre ω ε x ℓ i := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _ i
    show ∑ j, weight (flipW ε ω) 0 i j *
        (if (0 : ℕ) = 0 then netZ (flipW ε ω) x 0 j else relu (netZ (flipW ε ω) x 0 j)) = _
    simp only [pre, weight_flip, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show sgnL ε 0 j = 1 from rfl, show netZ (flipW ε ω) x 0 j = x j from rfl,
      show sh ω ε x 0 j = x j from rfl, if_pos trivial]
    ring
  | succ k ih =>
    intro hk i
    have hkL : k < L := by omega
    show ∑ j, weight (flipW ε ω) (k + 1) i j *
        (if k + 1 = 0 then netZ (flipW ε ω) x (k + 1) j
          else relu (netZ (flipW ε ω) x (k + 1) j)) = _
    simp only [pre, weight_flip, Finset.mul_sum, if_neg (Nat.succ_ne_zero k)]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih (by omega) j]
    have key : sgnL ε (k + 1) j * relu (sgnV ε k j * pre ω ε x k j) = sh ω ε x (k + 1) j := by
      show sgnV ε k j * relu (sgnV ε k j * pre ω ε x k j) = sh ω ε x (k + 1) j
      simp only [sh, dif_pos hkL]
      unfold sgnV
      rw [dif_pos hkL]
      exact sign_relu _ _
    rw [← key]
    ring

theorem output_flip {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (ε : MaskIndex n L → Bool)
    (x : Fin (n 0) → ℝ) : output (flipW ε ω) x = dropoutOutput ω (mk ω ε x) x := by
  funext q
  show netZ (flipW ε ω) x (L + 1) q = _
  rw [netZ_flip ω ε x L le_rfl q]
  have h1 : sgnV ε L q = 1 := by unfold sgnV; rw [dif_neg (lt_irrefl L)]
  rw [h1, one_mul]
  unfold dropoutOutput pre
  rw [dropout_eq_sh]

theorem mk_inj {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ) :
    Function.Injective (fun ε => mk ω ε x) := by
  intro ε ε' h
  have h' : mk ω ε x = mk ω ε' x := h
  have hsh : ∀ ℓ, sh ω ε x ℓ = sh ω ε' x ℓ := fun ℓ => by
    rw [← dropout_eq_sh, ← dropout_eq_sh, h']
  funext k
  have hk := congrFun h' k
  have hp : pre ω ε x k.1.val k.2 = pre ω ε' x k.1.val k.2 := by
    simp only [pre, hsh]
  change bitf (ε k) (pre ω ε x k.1.val k.2) = bitf (ε' k) (pre ω ε' x k.1.val k.2) at hk
  rw [hp] at hk
  exact bitf_inj hk

instance maskLaw_isProb {n : ℕ → ℕ} {L : ℕ} : IsProbabilityMeasure (maskLaw n L) := by
  unfold maskLaw; infer_instance

theorem maskLaw_singleton {n : ℕ → ℕ} {L : ℕ} (a : MaskIndex n L → Bool) :
    maskLaw n L {a} = ∏ _k : MaskIndex n L, ((Fintype.card Bool : ENNReal))⁻¹ := by
  rw [← Set.univ_pi_singleton, maskLaw, Measure.pi_pi]
  congr 1
  funext k
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]

theorem maskLaw_preimage {n : ℕ → ℕ} {L : ℕ}
    (e : (MaskIndex n L → Bool) → (MaskIndex n L → Bool)) (he : Function.Injective e)
    (A : Set (MaskIndex n L → Bool)) : maskLaw n L (e ⁻¹' A) = maskLaw n L A := by
  have hbij : Function.Bijective e := Finite.injective_iff_bijective.mp he
  have hmap : (maskLaw n L).map e = maskLaw n L := by
    apply Measure.ext_of_singleton
    intro a
    rw [Measure.map_apply (measurable_of_countable e) (measurableSet_singleton a)]
    obtain ⟨b, rfl⟩ := hbij.2 a
    rw [show e ⁻¹' {e b} = {b} from by ext y; simp [he.eq_iff]]
    rw [maskLaw_singleton, maskLaw_singleton]
  rw [← Measure.map_apply (measurable_of_countable e) (Set.to_countable A).measurableSet, hmap]

theorem sgnV_pm {n : ℕ → ℕ} {L : ℕ} (ε : MaskIndex n L → Bool) (ℓ : ℕ) (i : Fin (n (ℓ + 1))) :
    sgnV ε ℓ i = 1 ∨ sgnV ε ℓ i = -1 := by
  unfold sgnV
  split_ifs <;> simp

theorem sgnL_pm {n : ℕ → ℕ} {L : ℕ} (ε : MaskIndex n L → Bool) :
    ∀ (ℓ : ℕ) (j : Fin (n ℓ)), sgnL ε ℓ j = 1 ∨ sgnL ε ℓ j = -1
  | 0, _ => Or.inl rfl
  | ℓ + 1, j => sgnV_pm ε ℓ j

theorem flip_mp {n : ℕ → ℕ} {L : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_symm : μ.map (fun t : ℝ => -t) = μ) (ε : MaskIndex n L → Bool) :
    MeasurePreserving (flipW ε) (weightLaw n L μ) (weightLaw n L μ) := by
  have hc : ∀ k, coef ε k = 1 ∨ coef ε k = -1 := by
    intro k
    unfold coef
    rcases sgnV_pm ε k.1.val k.2.1 with h1 | h1 <;>
      rcases sgnL_pm ε k.1.val k.2.2 with h2 | h2 <;> rw [h1, h2] <;> norm_num
  have h1 : ∀ k, MeasurePreserving (fun t : ℝ => coef ε k * t) μ μ := by
    intro k
    rcases hc k with h | h <;> rw [h]
    · simp only [one_mul]
      exact MeasurePreserving.id μ
    · simp only [neg_one_mul]
      exact ⟨measurable_neg, hμ_symm⟩
  unfold weightLaw flipW
  exact measurePreserving_pi (fun _ => μ) (fun _ => μ) h1

theorem cont_weight {n : ℕ → ℕ} {L : ℕ} (ℓ : ℕ) (i : Fin (n (ℓ + 1))) (j : Fin (n ℓ)) :
    Continuous fun ω : Weights n L => weight ω ℓ i j := by
  unfold weight
  split_ifs
  · exact continuous_const.mul (continuous_apply _)
  · exact continuous_const

theorem cont_dropoutHidden {n : ℕ → ℕ} {L : ℕ} (ξ : MaskIndex n L → Bool)
    (x : Fin (n 0) → ℝ) :
    ∀ ℓ (i : Fin (n ℓ)), Continuous fun ω : Weights n L => dropoutHidden ω ξ x ℓ i := by
  intro ℓ
  induction ℓ with
  | zero => intro i; exact continuous_const
  | succ ℓ ih =>
    intro i
    simp only [dropoutHidden]
    exact continuous_const.mul
      (continuous_finsetSum _ fun j _ => (cont_weight ℓ i j).mul (ih j))

theorem cont_dropoutOutput {n : ℕ → ℕ} {L : ℕ} (ξ : MaskIndex n L → Bool)
    (x : Fin (n 0) → ℝ) : Continuous fun ω : Weights n L => dropoutOutput ω ξ x :=
  continuous_pi fun q => continuous_finsetSum _ fun j _ =>
    (cont_weight L q j).mul (cont_dropoutHidden ξ x L j)

theorem cont_netZ {n : ℕ → ℕ} {L : ℕ} (x : Fin (n 0) → ℝ) :
    ∀ ℓ (i : Fin (n ℓ)), Continuous fun ω : Weights n L => netZ ω x ℓ i := by
  intro ℓ
  induction ℓ with
  | zero => intro i; exact continuous_const
  | succ ℓ ih =>
    intro i
    simp only [netZ]
    refine continuous_finsetSum _ fun j _ => (cont_weight ℓ i j).mul ?_
    split_ifs
    · exact ih j
    · unfold relu
      exact (ih j).max continuous_const

theorem cont_output {n : ℕ → ℕ} {L : ℕ} (x : Fin (n 0) → ℝ) :
    Continuous fun ω : Weights n L => output ω x :=
  continuous_pi fun q => cont_netZ x (L + 1) q

end P54dae77a

open MeasureTheory ProbabilityTheory LesHouchesWidth in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_ac : μ ≪ volume) (hμ_symm : μ.map (fun t : ℝ => -t) = μ)
    (hμ_var : ∫ t, t ^ 2 ∂μ = 1)
    (L : ℕ) (hL : 1 ≤ L) (n : ℕ → ℕ) (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ)
    (x : Fin (n 0) → ℝ) (hx : x ≠ 0) :
    (weightLaw n L μ).map (fun ω => output ω x) =
      ((weightLaw n L μ).prod (maskLaw n L)).map (fun ωξ => dropoutOutput ωξ.1 ωξ.2 x) := by
  have := @P54dae77a.maskLaw_isProb n L
  have hout : Measurable (fun ω : Weights n L => output ω x) := (P54dae77a.cont_output x).measurable
  have hF : Measurable
      (fun ωξ : Weights n L × (MaskIndex n L → Bool) => dropoutOutput ωξ.1 ωξ.2 x) :=
    measurable_from_prod_countable_left fun ξ => (P54dae77a.cont_dropoutOutput ξ x).measurable
  have hG : Measurable
      (fun ωε : Weights n L × (MaskIndex n L → Bool) => output (P54dae77a.flipW ωε.2 ωε.1) x) :=
    measurable_from_prod_countable_left fun ε => hout.comp (P54dae77a.flip_mp μ hμ_symm ε).measurable
  ext s hs
  rw [Measure.map_apply hout hs, Measure.map_apply hF hs]
  have h1 : weightLaw n L μ ((fun ω => output ω x) ⁻¹' s) =
      ((weightLaw n L μ).prod (maskLaw n L))
        ((fun ωε : Weights n L × (MaskIndex n L → Bool) => output (P54dae77a.flipW ωε.2 ωε.1) x) ⁻¹' s) := by
    rw [Measure.prod_apply_symm (hG hs)]
    have hc : ∀ ε : MaskIndex n L → Bool, weightLaw n L μ ((fun ω => (ω, ε)) ⁻¹'
        ((fun ωε : Weights n L × (MaskIndex n L → Bool) => output (P54dae77a.flipW ωε.2 ωε.1) x) ⁻¹' s)) =
        weightLaw n L μ ((fun ω => output ω x) ⁻¹' s) := by
      intro ε
      exact (P54dae77a.flip_mp μ hμ_symm ε).measure_preimage (hout hs).nullMeasurableSet
    simp_rw [hc]
    rw [lintegral_const, measure_univ, mul_one]
  rw [h1, Measure.prod_apply (hG hs), Measure.prod_apply (hF hs)]
  apply lintegral_congr
  intro ω
  have hpre : (Prod.mk ω ⁻¹'
      ((fun ωε : Weights n L × (MaskIndex n L → Bool) => output (P54dae77a.flipW ωε.2 ωε.1) x) ⁻¹' s)) =
      (fun ε => P54dae77a.mk ω ε x) ⁻¹' (Prod.mk ω ⁻¹'
        ((fun ωξ : Weights n L × (MaskIndex n L → Bool) => dropoutOutput ωξ.1 ωξ.2 x) ⁻¹' s)) := by
    ext ε
    simp only [Set.mem_preimage, P54dae77a.output_flip]
  rw [hpre, P54dae77a.maskLaw_preimage _ (P54dae77a.mk_inj ω x)]
