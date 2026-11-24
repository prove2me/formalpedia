-- Prove2me | solution 1 for GlobalTheory.PartRedEval.kills_insert_of_evalLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:43.198808+00:00
-- url     : https://prove2.me/submissions/a8dc455c-1dcb-4054-8d9d-bf7888c4b1f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLaw
import Theorems.Thm_GlobalTheory_PartRedEval_fillAt_apply_of_notMem
import Theorems.Thm_GlobalTheory_PartRedEval_fillAt_add_single
import Theorems.Thm_GlobalTheory_PartRedEval_fillAt_insert
import Theorems.Thm_GlobalTheory_PartRedEval_exists_cball_single
import Theorems.Thm_GlobalTheory_PartRedEval_isLocallyConstant_mk
import Theorems.Thm_GlobalTheory_PartRedEval_exists_sep
import Theorems.Thm_GlobalTheory_PartRedEval_integrable_red
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_cball_mem_nhds
import Theorems.Thm_GlobalTheory_SplitWeil_conductor_exists
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball
import Theorems.Thm_GlobalTheory_StepData_IntM_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRedEval
open GlobalTheory.PartRed
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.PartRedEval
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ I → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.EvalLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β (insert e E) I := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν R Q _ _ _ _ M _ _ L w β E I e hI hK hL
  classical
  by_cases hE : e ∈ E
  · rwa [Finset.insert_eq_of_mem hE]
  intro Φ hΦ
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hψ1
  obtain ⟨s₁, hs₁⟩ := exists_cball_single Φ.2 e
  have hn : (fun u : k => u * w (Matrix.single e.1 e.2 1)) ⁻¹' cball c ∈ 𝓝 (0 : k) :=
    ((isOpen_cball c).preimage (by fun_prop)).mem_nhds (by simp [cball])
  obtain ⟨s, hs⟩ := exists_cball_subset (Filter.inter_mem (cball_mem_nhds s₁) hn)

  have hinv : ∀ u ∈ cball s, ∀ x, red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 u) = red ψ ν w β E I Φ.1 x := by
    intro u hu x
    unfold red
    congr 1
    funext y
    have h1 : w (Matrix.single e.1 e.2 u) = u * w (Matrix.single e.1 e.2 1) := by
      rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [fillAt_add_single β hE hI, hs₁ u (hs hu).1, map_add, neg_add, AddChar.map_add_eq_mul, h1,
      hc.eq_one (neg_mem_cball (hs hu).2), mul_one]
  let p : Matrix R Q k → k ⧸ ballGrp s := fun x => QuotientAddGroup.mk (x e.1 e.2)
  have hp : IsLocallyConstant p := (isLocallyConstant_mk s).comp_continuous (continuous_id.matrix_elem _ _)
  let P : k ⧸ ballGrp s → SB (Matrix R Q k) := fun q =>
    ⟨fun x => (if p x = q then 1 else 0) * Φ.1 x,
      (hp.comp fun a => if a = q then (1 : ℂ) else 0).mul Φ.2.1, Φ.2.2.mul_left⟩
  have hred : ∀ q x, red ψ ν w β E I (P q).1 x = (if p x = q then 1 else 0) * red ψ ν w β E I Φ.1 x := by
    intro q x
    unfold red
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [P, p, fillAt_apply_of_notMem β hE hI, mul_assoc]
  have hP : ∀ q, L (P q) = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with | H a => ?_
    by_cases ha : a - β e.1 e.2 ∈ cball s
    · refine hK _ (funext fun x => ?_)
      rw [hred]
      split_ifs with hx
      · have h1 : -x e.1 e.2 + a ∈ cball s := QuotientAddGroup.eq.mp hx
        have h2 : β e.1 e.2 - x e.1 e.2 ∈ cball s := by
          have := add_mem_cball h1 (neg_mem_cball ha)
          convert this using 1
          ring
        have h3 := congrFun hΦ x
        rw [← hinv _ h2, one_mul]
        simpa only [red, fillAt_insert β hE hI] using h3
      · simp
    · obtain ⟨b, hb, hb'⟩ := exists_sep hc s ha
      obtain ⟨Φ', h1, h2⟩ := hL b (P a)
      set z : ℂ := (ψ (b * (a - β e.1 e.2)) : ℂ) with hz
      have h3 : L (Φ' - z • P a) = 0 := by
        refine hK _ (funext fun x => ?_)
        have h4 : red ψ ν w β E I (Φ' - z • P a).1 x =
            red ψ ν w β E I Φ'.1 x - z * red ψ ν w β E I (P a).1 x := by
          unfold red
          rw [← integral_const_mul, ← integral_sub (integrable_red hψ ν w β E I Φ'.2 x)
            ((integrable_red hψ ν w β E I (P a).2 x).const_mul z)]
          congr 1
          funext y
          simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [h4, h2, hred]
        split_ifs with hx
        · have h5 : -a + x e.1 e.2 ∈ cball s := QuotientAddGroup.eq.mp hx.symm
          have h6 : b * (x e.1 e.2 - β e.1 e.2) = b * (a - β e.1 e.2) + b * (-a + x e.1 e.2) := by ring
          rw [h6, AddChar.map_add_eq_mul, hb' _ h5, mul_one, hz]
          simp
        · simp
      rw [map_sub, map_smul, h1] at h3
      have h7 : (1 - z) ≠ 0 := fun h => hb (Circle.ext (by rw [← hz, Circle.coe_one]; exact (sub_eq_zero.mp h).symm))
      have h8 : (1 - z) • L (P a) = 0 := by rw [sub_smul, one_smul, h3]
      exact (smul_eq_zero.mp h8).resolve_left h7
  have hfin : (p '' tsupport Φ.1).Finite := by
    letI : TopologicalSpace (k ⧸ ballGrp s) := ⊥
    haveI : DiscreteTopology (k ⧸ ballGrp s) := ⟨rfl⟩
    exact (IsCompact.image Φ.2.2 hp.continuous).finite_of_discrete
  have hsum : Φ = ∑ q ∈ hfin.toFinset, P q := by
    refine Subtype.ext (funext fun x => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, P, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Set.Finite.mem_toFinset]
    split_ifs with hx
    · rfl
    · exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨x, h, rfl⟩
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun q _ => hP q
end GlobalTheory.PartRedEval
