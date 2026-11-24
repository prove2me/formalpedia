-- Prove2me | solution 1 for GlobalTheory.RootEx.opE_om_target_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:45.79071+00:00
-- url     : https://prove2.me/submissions/f9ed86c1-228b-4dad-af29-f7666e9e3c31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Theorems.Thm_GlobalTheory_RootEx_TargetUnip_det_linPart
import Theorems.Thm_GlobalTheory_RootEx_TargetUnip_mul_affPt
import Theorems.Thm_GlobalTheory_RootEx_TargetUnip_ch_mul_affPt
import Theorems.Thm_GlobalTheory_RootEx_Radical_unipotent_radical_basic
import Theorems.Thm_GlobalTheory_SplitWeil_integral_comp_mulVec_eq_smul
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory.RootEx.TargetUnip
namespace GlobalTheory.RootEx
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), ∀ g ∈ N k n c p, opE ψ ν p (om μ 1 g Φ) = (ψ (-simpleSum g) : ℂ) • opE ψ ν p Φ := by
  classical
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ ν _ μ Φ g hg
  obtain ⟨hN, hadd, hdet, -⟩ := GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c p
  have hg' : g⁻¹ ∈ N k n c p := inv_mem hg
  have hh : InN p g⁻¹ := (hN _).1 hg'
  have hs1 : simpleSum (1 : GL (n ⊕ Fin c) k) = 0 := by
    have := hadd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact left_eq_add.1 this
  have hs : simpleSum g⁻¹ = -simpleSum g := by
    have := hadd g hg g⁻¹ hg'
    rw [mul_inv_cancel, hs1] at this
    linear_combination -this
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  have hom : ∀ x, om μ 1 g Φ x = Φ ((g⁻¹).val * x) := by
    intro x
    simp [om, hdet g hg, hn1]
  haveI := secondCountable k
  funext x₀
  let F : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ := fun e =>
    Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)
  let t : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k :=
    fun a => ((g⁻¹).val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2
  let L := Matrix.GeneralLinearGroup.mkOfDetNeZero (linPart (n' := n') p (g⁻¹).val)
    (by rw [det_linPart hh]; exact one_ne_zero)
  have hL : Matrix.GeneralLinearGroup.det L = 1 := by
    ext
    exact det_linPart hh
  have key : ∀ e, om μ 1 g Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) =
      (ψ (-simpleSum g) : ℂ) * F (L.val.mulVec e + t) := by
    intro e
    have h1 := mul_affPt hh x₀ e
    have h2 := ch_mul_affPt hh x₀ e
    have h3 : F (L.val.mulVec e + t) = Φ ((g⁻¹).val * affPt p x₀ e) *
        (ψ (-ch ((g⁻¹).val * affPt p x₀ e)) : ℂ) := by
      rw [h1]; rfl
    rw [h3, h2, hs, hom, mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  have hcov := integral_comp_mulVec_eq_smul ν L
    (fun e => F (e + t))
  rw [hL, hn1, inv_one, one_smul, integral_add_right_eq_self] at hcov
  simp only [opE, Pi.smul_apply, smul_eq_mul, key]
  rw [integral_const_mul, hcov]
end GlobalTheory.RootEx
