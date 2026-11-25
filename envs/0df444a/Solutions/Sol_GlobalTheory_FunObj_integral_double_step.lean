-- Prove2me | solution 1 for GlobalTheory.FunObj.integral_double_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:05:07.749278+00:00
-- url     : https://prove2.me/submissions/ce42f343-88db-478f-94d6-732d4a7ad971

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
import Theorems.Thm_GlobalTheory_FunObj_flatStep_eq_flCol
import Theorems.Thm_GlobalTheory_FunObj_flatStep_eq_flRow
import Theorems.Thm_GlobalTheory_FunObj_measurePreserving_comp_equiv
import Theorems.Thm_GlobalTheory_FunObj_integral_pair_eq_contr
import Theorems.Thm_GlobalTheory_LocFlat_flat_SB_onto
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
  {ψ : AddChar k Circle} (ν : Measure k) [ν.IsAddHaarMeasure]
open Classical
namespace GlobalTheory.FunObj
theorem _root_.solution (hψ : Continuous ψ) {c c' : ℕ} (hc : Even c) (hc' : Odd c')
    {Φ₁ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {Φ₂ : Matrix (n'' ⊕ Fin c') (n ⊕ Fin (c' + 1)) k → ℂ}
    (h₁ : Φ₁ ∈ SB _) (h₂ : Φ₂ ∈ SB _) (x₁ : Matrix n n' k) (x₂ : Matrix n'' n k) :
    ∫ p : (KeptVar n c n' → k) × (KeptVar n'' c' n → k), flatStep ψ ν Φ₁ x₁ p.1 * flatStep ψ ν Φ₂ x₂ p.2 *
      (ψ (-∑ r, p.2 (rowIx hc' r) * p.1 (colIx hc r)) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) =
      contr ψ ν (flCol ψ ν (c / 2 + 1) Φ₁) (flRow ψ ν (c' / 2 + 1) Φ₂) (x₁, x₂) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hp := hc'.pos
  rw [← integral_pair_eq_contr ν hψ
    (((flat_SB_onto k ψ ν hψ inferInstance n n' c (c / 2 + 1) (by omega)).1 (by omega)).1 Φ₁ h₁)
    (((flat_SB_onto k ψ ν hψ inferInstance n'' n c' (c' / 2 + 1) (by omega)).2 (by omega)).1 Φ₂ h₂)]
  have h : MeasurePreserving ((MeasurableEquiv.piCongrLeft (fun _ => k) (colEquiv (n := n) (n' := n') hc)).symm.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ => k) (rowEquiv (n := n'') (n' := n) hc')).symm) _ _ :=
    (measurePreserving_comp_equiv ν (colEquiv hc)).prod (measurePreserving_comp_equiv ν (rowEquiv hc'))
  rw [← h.integral_comp']
  simp only [flatStep_eq_flCol ψ ν hc, flatStep_eq_flRow ψ ν hc']
  rfl
end GlobalTheory.FunObj
