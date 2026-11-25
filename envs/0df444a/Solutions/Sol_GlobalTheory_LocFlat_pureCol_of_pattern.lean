-- Prove2me | solution 1 for GlobalTheory.LocFlat.pureCol_of_pattern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:59.330918+00:00
-- url     : https://prove2.me/submissions/967e560a-9b09-4f80-b892-afd6e5060d90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPosition
import Theorems.Thm_GlobalTheory_LocFlat_PureColPf_affPt_col
import Theorems.Thm_GlobalTheory_LocFlat_PureColPf_om_one_one
import Theorems.Thm_GlobalTheory_LocFlat_PureColPf_Phi_add_colAt
import Theorems.Thm_GlobalTheory_LocFlat_PureColPf_mem_box_of_Phi_ne_zero
import Theorems.Thm_GlobalTheory_StepData_Chain_ofType_regular
import Theorems.Thm_GlobalTheory_StepData_volNat_Cgrp_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PureColPf
namespace GlobalTheory.LocFlat.PureColPf
namespace _root_.GlobalTheory.LocFlat
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
      S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureCol S t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hpat hex
  haveI := hν.1
  intro j c H r hr
  obtain ⟨C, hC, hCe⟩ := hex j (c + 1) (by omega) (r + 1) (by omega) (by omega) (by have := S.odd; omega)
  have hreg := (Chain.ofType_regular S.P S.μ S.tame (fun j c h => typeFrame S.ϖ (stdOrd (Fin κ) t j c h))
    (LatFrame.refl k _)).2.2 (j + 1) (c + 1) (by omega)
  have hvol := volNat_Cgrp_pos ν (J := ((S.T t).lev (j + 1) (c + 1) (by omega)).J) hreg.1 hreg.2.1
    ((S.T t).bas (j + 1) (c + 1) (by omega)) 1
  set V := volNat ν ((S.T t).bas (j + 1) (c + 1) (by omega)) (Cgrp ((S.T t).lev (j + 1) (c + 1) (by omega)).J 1)
    with hV
  refine ⟨C * V, mul_pos hC hvol, fun x => ?_⟩
  have hent : ∀ x₀, (S.T t).entry S.ψ ν j c H 1 1 x₀ =
      ((V⁻¹ : ℝ) : ℂ) * opE S.ψ ν 1 ((S.T t).Phi j (c + 1) (by omega)) x₀ := by
    intro x₀
    simp only [Chain.entry, xi, flat, om_one_one, hV]
  by_cases hy : (fun a => x a (Sum.inr ())) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹
  · rw [if_pos hy, mul_one, hent]
    have e : flCol S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x =
        opE S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x.toCols₁ := by
      unfold flCol
      congr 1
      funext z
      exact Phi_add_colAt S t j c H r _ hy z
    rw [e, hCe, Pi.smul_apply, smul_eq_mul]
    have hV0 : (V : ℂ) ≠ 0 := by exact_mod_cast hvol.ne'
    push_cast
    field_simp
  · rw [if_neg hy, mul_zero]
    unfold flCol opE
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
    have h0 : (S.T t).Phi j (c + 1) (by omega) (affPt (r + 1) x.toCols₁ e +
        colAt (XIx (Fin κ) t j) (c + 1) (r + 1) fun a => x a (Sum.inr ())) = 0 := by
      by_contra hne
      exact hy (mem_box_of_Phi_ne_zero S t hpat j c H r hr _
        (fun a => affPt_col _ _ _ _ _ rfl) _ hne)
    simp only [h0, zero_mul, Pi.zero_apply]
end _root_.GlobalTheory.LocFlat
end GlobalTheory.LocFlat.PureColPf
