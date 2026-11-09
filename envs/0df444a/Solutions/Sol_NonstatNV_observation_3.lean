-- Prove2me | solution 1 for NonstatNV.observation_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:13:41.280018+00:00
-- url     : https://prove2.me/submissions/78dc25e1-5b18-4de9-9704-ebefa2c1e76c

import Definitions.Def_NonstatNV_Model_Standing
import Definitions.Def_NonstatNV_Model_LipschitzCost
import Definitions.Def_NonstatNV_Model_IsInstance
import Definitions.Def_NonstatNV_Model_IsPolicy
import Definitions.Def_NonstatNV_Model_intervalRegret

open MeasureTheory

open NonstatNV in
theorem solution (M : Model) (ℓ : ℝ) (hM : M.Standing) (hℓ : M.LipschitzCost ℓ)
    (T : ℕ) (q : ℕ → (ℕ → ℝ) → ℝ) (hq : M.IsPolicy T q) (μhat : ℕ → (ℕ → ℝ) → ℝ)
    (μ b h : ℕ → ℝ) (hinst : M.IsInstance T μ b h) (lo hi : ℕ) (hlo : 1 ≤ lo) (hhi : hi ≤ T)
    (hμhat : ∀ t ∈ Finset.Icc lo hi, Measurable (μhat t) ∧ ∀ ω, μhat t ω ∈ Set.Icc M.μmin M.μmax ∧
      ∀ q' ∈ M.Q, M.cost (μhat t ω) (b t) (h t) (q t ω) ≤ M.cost (μhat t ω) (b t) (h t) q') :
    M.intervalRegret μ b h q lo hi ≤
      2 * ℓ * ∫ ω, (∑ t ∈ Finset.Icc lo hi, |μhat t ω - μ t|) ∂(M.demandLaw μ) := by
  obtain ⟨hℓ0, hL⟩ := hℓ
  have hQne : Nonempty M.Q := hM.2.2.2.1.to_subtype
  have hcost0 : ∀ μ' b' h' q', 0 ≤ b' → 0 ≤ h' → 0 ≤ M.cost μ' b' h' q' := by
    intro μ' b' h' q' hb hh
    unfold Model.cost
    exact integral_nonneg fun d =>
      add_nonneg (mul_nonneg hb (le_max_right _ _)) (mul_nonneg hh (le_max_right _ _))
  have hT : ∀ t ∈ Finset.Icc lo hi, t ∈ Finset.Icc 1 T := by
    intro t ht
    rw [Finset.mem_Icc] at ht ⊢
    omega
  have hterm : ∀ t ∈ Finset.Icc lo hi, ∀ ω,
      0 ≤ M.cost (μ t) (b t) (h t) (q t ω) - M.opt (μ t) (b t) (h t) ∧
      M.cost (μ t) (b t) (h t) (q t ω) - M.opt (μ t) (b t) (h t) ≤
        2 * ℓ * |μhat t ω - μ t| := by
    intro t ht ω
    obtain ⟨hμt, hbt, hht⟩ := hinst t (hT t ht)
    obtain ⟨_, hqQ, _⟩ := hq t (hT t ht)
    obtain ⟨_, hμh⟩ := hμhat t ht
    obtain ⟨hμhω, hopt⟩ := hμh ω
    have hbdd : BddBelow (Set.range fun q' : M.Q => M.cost (μ t) (b t) (h t) q') :=
      ⟨0, by rintro _ ⟨q', rfl⟩; exact hcost0 _ _ _ _ hbt.1 hht.1⟩
    refine ⟨?_, ?_⟩
    · have : M.opt (μ t) (b t) (h t) ≤ M.cost (μ t) (b t) (h t) (q t ω) :=
        ciInf_le hbdd ⟨q t ω, hqQ ω⟩
      linarith
    · have hlow : M.cost (μ t) (b t) (h t) (q t ω) - 2 * ℓ * |μhat t ω - μ t| ≤
          M.opt (μ t) (b t) (h t) := by
        unfold Model.opt
        refine le_ciInf fun q' => ?_
        have l1 := hL (b t) hbt (h t) hht (q t ω) (hqQ ω) (μ t) hμt (μhat t ω) hμhω
        have l2 := hL (b t) hbt (h t) hht q' q'.2 (μhat t ω) hμhω (μ t) hμt
        have o := hopt q' q'.2
        rw [abs_le] at l1 l2
        rw [abs_sub_comm] at l1
        have hab := abs_nonneg (μhat t ω - μ t)
        linarith [l1.1, l1.2, l2.1, l2.2]
      linarith
  haveI : IsProbabilityMeasure (M.demandLaw μ) := by
    unfold Model.demandLaw; infer_instance
  have hgi : Integrable (fun ω => ∑ t ∈ Finset.Icc lo hi, 2 * ℓ * |μhat t ω - μ t|)
      (M.demandLaw μ) := by
    refine integrable_finset_sum _ fun t ht => ?_
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound
      (((hμhat t ht).1.sub_const (μ t)).abs.aestronglyMeasurable) (M.μmax - M.μmin) ?_
    refine ae_of_all _ fun ω => ?_
    obtain ⟨hμt, _, _⟩ := hinst t (hT t ht)
    obtain ⟨h1, _⟩ := (hμhat t ht).2 ω
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    obtain ⟨a1, a2⟩ := hμt
    obtain ⟨c1, c2⟩ := h1
    constructor <;> linarith
  unfold Model.intervalRegret
  calc ∫ ω, (∑ t ∈ Finset.Icc lo hi,
        (M.cost (μ t) (b t) (h t) (q t ω) - M.opt (μ t) (b t) (h t))) ∂(M.demandLaw μ)
      ≤ ∫ ω, (∑ t ∈ Finset.Icc lo hi, 2 * ℓ * |μhat t ω - μ t|) ∂(M.demandLaw μ) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω => ?_) hgi (ae_of_all _ fun ω => ?_)
        · exact Finset.sum_nonneg fun t ht => (hterm t ht ω).1
        · exact Finset.sum_le_sum fun t ht => (hterm t ht ω).2
    _ = 2 * ℓ * ∫ ω, (∑ t ∈ Finset.Icc lo hi, |μhat t ω - μ t|) ∂(M.demandLaw μ) := by
        rw [← integral_const_mul]
        congr 1
        funext ω
        rw [Finset.mul_sum]
