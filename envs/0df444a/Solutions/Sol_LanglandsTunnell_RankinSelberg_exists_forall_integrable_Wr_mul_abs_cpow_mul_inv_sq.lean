-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_Wr_mul_abs_cpow_mul_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c7b6b037-6603-57a1-b34b-2353052c93cb

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_Wr_mul_abs_cpow_mul_inv_sq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in
theorem solution
    (P : RealArchParam)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hWr1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (par₀ : ZMod 2) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      MeasureTheory.Integrable
        (fun t : ℝ => Wr par₀ default t * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by

  set fp : ℝ → ℂ := fun t => Wr par₀ default t with hfp
  set fm : ℝ → ℂ := fun t => Wr par₀ default (-t) with hfm
  have hreal : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal (default : InfinitePlace ℚ)

  have v0 : (0 : ZMod 2).val = 0 := by decide
  have v1 : (1 : ZMod 2).val = 1 := by decide
  have v01 : ((0 : ZMod 2) + 1).val = 1 := by decide
  have v11 : ((1 : ZMod 2) + 1).val = 0 := by decide
  have zcases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by
    intro b; obtain ⟨n, hn⟩ := b
    interval_cases n
    · left; rfl
    · right; rfl
  have sign_succ : ∀ b : ZMod 2, (-1 : ℂ) ^ (b + 1).val = -(-1 : ℂ) ^ b.val := by
    intro b; rcases zcases b with rfl | rfl
    · rw [v01, v0]; norm_num
    · rw [v11, v1]; norm_num
  have sign_sq : ∀ b : ZMod 2, (-1 : ℂ) ^ b.val * (-1 : ℂ) ^ b.val = 1 := by
    intro b; rw [← mul_pow]; norm_num

  have two_signs : ∀ (ε : ℂ) (s₁ s₂ : ℝ),
      (∀ s : ℂ, s₁ < s.re → MellinConvergent (fun t : ℝ => (fp t + ε * fm t) / (t : ℂ)) s) →
      (∀ s : ℂ, s₂ < s.re → MellinConvergent (fun t : ℝ => (fp t + -ε * fm t) / (t : ℂ)) s) →
      ε ≠ 0 →
      ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
        MellinConvergent (fun t : ℝ => fp t / (t : ℂ)) s ∧ MellinConvergent (fun t : ℝ => fm t / (t : ℂ)) s := by
    intro ε s₁ s₂ h1 h2 hε
    refine ⟨max s₁ s₂, fun s hs => ?_⟩
    have H1 := h1 s (lt_of_le_of_lt (le_max_left _ _) hs)
    have H2 := h2 s (lt_of_le_of_lt (le_max_right _ _) hs)
    unfold MellinConvergent at H1 H2 ⊢
    constructor
    · have h12 : IntegrableOn (fun t : ℝ => (2 : ℂ)⁻¹ * ((t : ℂ) ^ (s - 1) • ((fp t + ε * fm t) / (t : ℂ)) +
          (t : ℂ) ^ (s - 1) • ((fp t + -ε * fm t) / (t : ℂ)))) (Set.Ioi 0) := (H1.add H2).const_mul _
      refine IntegrableOn.congr_fun h12 (fun t _ => ?_) measurableSet_Ioi
      simp only [smul_eq_mul]
      ring
    · have h12 : IntegrableOn (fun t : ℝ => (2 * ε)⁻¹ * ((t : ℂ) ^ (s - 1) • ((fp t + ε * fm t) / (t : ℂ)) -
          (t : ℂ) ^ (s - 1) • ((fp t + -ε * fm t) / (t : ℂ)))) (Set.Ioi 0) := (H1.sub H2).const_mul _
      refine IntegrableOn.congr_fun h12 (fun t _ => ?_) measurableSet_Ioi
      simp only [smul_eq_mul]
      field_simp
      ring
  have KEY : ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
      MellinConvergent (fun t : ℝ => fp t / (t : ℂ)) s ∧ MellinConvergent (fun t : ℝ => fm t / (t : ℂ)) s := by
    rcases P with ⟨u₁, a₁, u₂, a₂⟩ | ⟨u₀, k, hk⟩
    ·
      by_cases h12 : a₂ = a₁
      · subst a₂
        by_cases hp : par₀ = a₁
        ·
          have hsym := hWr1 par₀ default hreal u₁ u₂ a₁ rfl hp
          obtain ⟨s₀, h4⟩ := hWr4 par₀ default hreal par₀ (Or.inl rfl)
          refine ⟨s₀, fun s hs => ?_⟩
          have H := (h4 s hs).1
          subst hp
          have hfm' : ∀ t : ℝ, fm t = (-1 : ℂ) ^ par₀.val * fp t := fun t => hsym t
          unfold MellinConvergent at H ⊢
          have Hp : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (fp t / (t : ℂ))) (Set.Ioi 0) := by
            have h2 : IntegrableOn (fun t : ℝ => (2 : ℂ)⁻¹ * ((t : ℂ) ^ (s - 1) •
                ((fp t + (-1 : ℂ) ^ par₀.val * fm t) / (t : ℂ)))) (Set.Ioi 0) := H.const_mul _
            refine IntegrableOn.congr_fun h2 (fun t _ => ?_) measurableSet_Ioi
            simp only [smul_eq_mul, hfm', ← mul_assoc, sign_sq, one_mul]
            ring
          refine ⟨Hp, ?_⟩
          have h3 : IntegrableOn (fun t : ℝ => (-1 : ℂ) ^ par₀.val * ((t : ℂ) ^ (s - 1) • (fp t / (t : ℂ)))) (Set.Ioi 0) :=
            Hp.const_mul _
          refine IntegrableOn.congr_fun h3 (fun t _ => ?_) measurableSet_Ioi
          simp only [smul_eq_mul, hfm']
          ring
        ·
          have hp' : par₀ = a₁ + 1 := by
            rcases zcases a₁ with rfl | rfl <;> rcases zcases par₀ with rfl | rfl
            · exact absurd rfl hp
            · rfl
            · rfl
            · exact absurd rfl hp
          obtain ⟨s₁, h3⟩ := hWr3 par₀ default hreal u₁ u₂ a₁ rfl hp'
          obtain ⟨s₂, h4⟩ := hWr4 par₀ default hreal par₀ (Or.inl rfl)
          refine two_signs ((-1 : ℂ) ^ a₁.val) s₁ s₂ (fun s hs => (h3 s hs).1) (fun s hs => ?_) (by
            apply pow_ne_zero; norm_num)
          have hsgn : (-1 : ℂ) ^ par₀.val = -(-1 : ℂ) ^ a₁.val := by rw [hp', sign_succ]
          have := (h4 s hs).1
          rw [hsgn] at this
          exact this
      ·
        have hcs : RealArchParam.centralSign (RealArchParam.principal u₁ a₁ u₂ a₂) = 1 := by
          show a₁ + a₂ = 1
          rcases zcases a₁ with rfl | rfl <;> rcases zcases a₂ with rfl | rfl
          · exact absurd rfl h12
          · rfl
          · rfl
          · exact absurd rfl h12
        obtain ⟨s₁, h4a⟩ := hWr4 par₀ default hreal par₀ (Or.inl rfl)
        obtain ⟨s₂, h4b⟩ := hWr4 par₀ default hreal (par₀ + 1) (Or.inr (by rw [hcs]))
        refine two_signs ((-1 : ℂ) ^ par₀.val) s₁ s₂ (fun s hs => (h4a s hs).1) (fun s hs => ?_) (by
          apply pow_ne_zero; norm_num)
        have := (h4b s hs).1
        rw [sign_succ] at this
        exact this
    ·
      have hvan := hWr2 par₀ default hreal u₀ k hk rfl
      obtain ⟨s₀, h4⟩ := hWr4 par₀ default hreal par₀ (Or.inl rfl)
      refine ⟨s₀, fun s hs => ?_⟩
      have H := (h4 s hs).1
      unfold MellinConvergent at H ⊢
      have hfm0 : ∀ t : ℝ, 0 < t → fm t = 0 := by
        intro t ht
        have h := hvan (-t) (by linarith)
        rw [Complex.ofReal_neg] at h
        exact h
      constructor
      · refine IntegrableOn.congr_fun H (fun t ht => ?_) measurableSet_Ioi
        show (t : ℂ) ^ (s - 1) • ((fp t + (-1 : ℂ) ^ par₀.val * fm t) / (t : ℂ)) = (t : ℂ) ^ (s - 1) • (fp t / (t : ℂ))
        rw [hfm0 t ht, mul_zero, add_zero]
      · refine IntegrableOn.congr_fun integrableOn_zero (fun t ht => ?_) measurableSet_Ioi
        show (0 : ℂ) = (t : ℂ) ^ (s - 1) • (fm t / (t : ℂ))
        rw [hfm0 t ht, zero_div, smul_zero]

  obtain ⟨σ₁, hK⟩ := KEY
  refine ⟨σ₁ + 1 / 2, fun s hs => ?_⟩
  obtain ⟨Hp, Hm⟩ := hK (s - 1 / 2) (by simp; linarith)
  unfold MellinConvergent at Hp Hm

  have hpos : IntegrableOn
      (fun t : ℝ => Wr par₀ default t * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) (Set.Ioi 0) := by
    refine Hp.congr_fun (fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    beta_reduce
    rw [abs_of_pos ht0, smul_eq_mul]
    show (t : ℂ) ^ (s - 1 / 2 - 1) * (Wr par₀ default t / (t : ℂ)) = Wr par₀ default t * (t : ℂ) ^ (s - 1 / 2) * (((t ^ 2)⁻¹ : ℝ) : ℂ)
    rw [Complex.cpow_sub _ _ htc, Complex.cpow_one]
    push_cast
    field_simp

  have hneg : IntegrableOn
      (fun t : ℝ => Wr par₀ default t * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) (Set.Iio 0) := by
    have hmp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume := Measure.measurePreserving_neg volume
    have hme : MeasurableEmbedding (Neg.neg : ℝ → ℝ) := (MeasurableEquiv.neg ℝ).measurableEmbedding
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Iio 0 = Set.Ioi 0 := by
      ext t; simp
    rw [← hmp.integrableOn_comp_preimage hme, hpre]
    refine Hm.congr_fun (fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    simp only [Function.comp_apply, abs_neg, abs_of_pos ht0, neg_sq, smul_eq_mul, Complex.ofReal_neg]
    show (t : ℂ) ^ (s - 1 / 2 - 1) * (Wr par₀ default (-(t : ℂ)) / (t : ℂ)) = Wr par₀ default (-(t : ℂ)) * (t : ℂ) ^ (s - 1 / 2) * (((t ^ 2)⁻¹ : ℝ) : ℂ)
    rw [Complex.cpow_sub _ _ htc, Complex.cpow_one]
    push_cast
    field_simp

  have hIci : IntegrableOn
      (fun t : ℝ => Wr par₀ default t * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).2 hpos
  have := hneg.union hIci
  rwa [Set.Iio_union_Ici, integrableOn_univ] at this

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_Wr_mul_abs_cpow_mul_inv_sq
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_Wr_mul_abs_cpow_mul_inv_sq (solution)
