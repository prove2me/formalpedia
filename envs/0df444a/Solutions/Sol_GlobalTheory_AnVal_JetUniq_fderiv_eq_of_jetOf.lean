-- Prove2me | solution 1 for GlobalTheory.AnVal.JetUniq.fderiv_eq_of_jetOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:41.587971+00:00
-- url     : https://prove2.me/submissions/ccbd51ef-b9ca-4729-bece-cbdd80cf5756

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_coeff_tay_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_sum_single_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnVal.JetUniq
private theorem snd_aeval_eps_monomial_eq_ite {κ : Type} [DecidableEq κ] (ℓ : κ) (e : κ →₀ ℕ) (c : ℂ) :
    (MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0)
      (MvPolynomial.monomial e c)).snd = if e = Finsupp.single ℓ 1 then c else 0 := by
  rw [MvPolynomial.aeval_monomial]
  split_ifs with he
  · subst he
    simp [Finsupp.prod_single_index]
    rfl
  · have hp : (e.prod fun i k => (if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0) ^ k).snd = 0 := by
      by_cases hs : ∃ i ∈ e.support, i ≠ ℓ
      · obtain ⟨i, hi, hiℓ⟩ := hs
        rw [Finsupp.prod, Finset.prod_eq_zero hi (by rw [if_neg hiℓ]; exact zero_pow (Finsupp.mem_support_iff.mp hi))]
        rfl
      · have he' : e = Finsupp.single ℓ (e ℓ) := by
          ext i
          by_cases hi : i = ℓ
          · subst hi
            simp
          · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
            by_contra h0
            exact hs ⟨i, Finsupp.mem_support_iff.mpr h0, hi⟩
        have hk : e ℓ ≠ 1 := fun h1 => he (by rw [he', h1])
        rw [he', Finsupp.prod_single_index (by simp), if_pos rfl]
        rcases Nat.lt_or_gt_of_ne hk with h0 | h2
        · rw [show e ℓ = 0 by omega, pow_zero]
          rfl
        · obtain ⟨j, hj⟩ : ∃ j, e ℓ = j + 2 := ⟨e ℓ - 2, by omega⟩
          rw [hj, pow_add, pow_two, DualNumber.eps_mul_eps, mul_zero]
          rfl
    rw [TrivSqZeroExt.snd_mul, hp, smul_zero, zero_add]
    exact smul_zero _
private theorem single_one_mem_degLE_succ {κ : Type} [Fintype κ] [DecidableEq κ] (k : ℕ) (ℓ : κ) :
    Finsupp.single ℓ 1 ∈ (degLE (k + 1) : Finset (κ →₀ ℕ)) := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨fun i => ⟨Finsupp.single ℓ 1 i, by rw [Finsupp.single_apply]; split_ifs <;> omega⟩,
    Finset.mem_univ _, ?_⟩, ?_⟩
  · ext i
    simp
  · simp [Finsupp.sum_single_index]
private theorem snd_jetTan_psJet_succ_eq_coeff_single {κ : Type} [Fintype κ] [DecidableEq κ] (k : ℕ) (ℓ : κ)
    (F : MvPowerSeries κ ℂ) :
    (jetTan ℓ (psJet (k + 1) F) : DualNumber ℂ).snd = MvPowerSeries.coeff (Finsupp.single ℓ 1) F := by
  change (MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0)
    (psTrunc (k + 1) F)).snd = _
  unfold psTrunc
  rw [map_sum, TrivSqZeroExt.snd_sum]
  simp_rw [snd_aeval_eps_monomial_eq_ite]
  rw [Finset.sum_ite_eq', if_pos (single_one_mem_degLE_succ k ℓ)]
end GlobalTheory.AnVal.JetUniq
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetUniq
namespace GlobalTheory.AnVal.JetUniq
theorem _root_.solution {g : ℕ} (m : ℕ) (θ θ' : (Fin g → ℂ) → ℂ)
    (h : PullbackSections.jetOf (m + 1) θ = PullbackSections.jetOf (m + 1) θ') : fderiv ℂ θ 0 = fderiv ℂ θ' 0 := by
  have hc : ∀ j : Fin g, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (PullbackSections.tay θ 0) =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (PullbackSections.tay θ' 0) := by
    intro j
    have := congrArg (fun a => (jetTan ((0 : Fin 1), j) a : DualNumber ℂ).snd) h
    change (jetTan ((0 : Fin 1), j) (psJet (m + 1) (PullbackSections.tay θ 0)) : DualNumber ℂ).snd =
      (jetTan ((0 : Fin 1), j) (psJet (m + 1) (PullbackSections.tay θ' 0)) : DualNumber ℂ).snd at this
    rwa [snd_jetTan_psJet_succ_eq_coeff_single, snd_jetTan_psJet_succ_eq_coeff_single] at this
  have hd : ∀ j : Fin g, fderiv ℂ θ 0 (Pi.single j 1) = fderiv ℂ θ' 0 (Pi.single j 1) := by
    intro j
    have hm : ∀ φ : (Fin g → ℂ) → ℂ,
        PullbackSections.mD φ 0 (PullbackSections.dirs (Finsupp.single ((0 : Fin 1), j) 1)) = fderiv ℂ φ 0 (Pi.single j 1) := by
      intro φ
      have key : ∀ (w : Fin g → ℂ) (l : List (Fin g → ℂ)), l = [w] →
          iteratedFDeriv ℂ l.length φ 0 (fun i => l.get i) = fderiv ℂ φ 0 w := by
        intro w l hl
        subst hl
        exact iteratedFDeriv_one_apply _
      simp only [PullbackSections.dirs, Finsupp.toMultiset_single, one_smul, Multiset.map_singleton]
      unfold PullbackSections.mD PullbackSections.lD
      exact key _ _ (Multiset.toList_singleton _)
    have e1 := PullbackSections.coeff_tay_zero θ (Finsupp.single ((0 : Fin 1), j) 1)
    have e2 := PullbackSections.coeff_tay_zero θ' (Finsupp.single ((0 : Fin 1), j) 1)
    rw [hc j] at e1
    rw [← hm θ, ← hm θ']
    exact e1.symm.trans e2
  ext v
  rw [PullbackSections.sum_single_smul v]
  simp only [map_sum, map_smul, hd]
end GlobalTheory.AnVal.JetUniq
