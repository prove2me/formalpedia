-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:32.727336+00:00
-- url     : https://prove2.me/submissions/4468b519-ebcf-46e4-94a3-370b2f24babc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_Dp_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_mem_unitGL_entries
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_step
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_continuous_of_val
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_continuous_map_gl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GlobalTheory.CompanionTheory.TwContraction
theorem _root_.solution (U : Subgroup (GL (Fin n) F)) (hU : (U : Set (GL (Fin n) F)) = iwahori (m := n) F)
    (hcpt : IsCompact (iwahori (m := n) F))
    (τ : F ≃+* F) (hτ : ∀ a, valuation F (τ a) = valuation F a)
    (hτU : ∀ g ∈ U, Matrix.GeneralLinearGroup.map (τ : F →+* F) g ∈ U)
    (ρ : ValueGroupWithZero F) (hρ1 : ρ < 1)
    (hunif : ∀ a : F, valuation F a < 1 → valuation F a ≤ ρ)
    (e : Fin n → F) (he : ∀ i, e i ≠ 0)
    (hc : ∀ i l, i < l → valuation F (e i) ≤ ρ * valuation F (e l))
    (x : GL (Fin n) F) (hx : (x : Matrix (Fin n) (Fin n) F) = Matrix.diagonal e)
    (δ : GL (Fin n) F) (hδ : δ ∈ iwDouble F x) :
    ∃ m ∈ iwahori (m := n) F, ∃ t ∈ torusO F,
      m⁻¹ * δ * Matrix.GeneralLinearGroup.map (τ : F →+* F) m = x * t := by
  have hUI : ∀ g, g ∈ U ↔ g ∈ iwahori (m := n) F := fun g => by
    rw [← hU]; rfl
  let f : GL (Fin n) F → GL (Fin n) F := fun m =>
    x⁻¹ * m⁻¹ * δ * Matrix.GeneralLinearGroup.map (τ : F →+* F) m
  have hf : Continuous f :=
    ((continuous_const.mul continuous_inv).mul continuous_const).mul
      (continuous_map_gl _ (continuous_of_val τ hτ))
  let S : ℕ → Set (GL (Fin n) F) := fun j =>
    {m | m ∈ iwahori (m := n) F ∧ f m ∈ iwahori (m := n) F ∧
      ∀ i l, i ≠ l → valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j}
  have hclosedI : IsClosed (iwahori (m := n) F) := hcpt.isClosed
  have hSc : ∀ j, IsClosed (S j) := fun j => by
    have h1 : IsClosed {m : GL (Fin n) F | ∀ i l, i ≠ l →
        valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun i => isClosed_iInter fun l => isClosed_iInter fun _ => ?_
      have hcont : Continuous fun m : GL (Fin n) F => (f m : Matrix (Fin n) (Fin n) F) i l :=
        (Units.continuous_val.comp hf).matrix_elem i l
      exact (IsNonarchimedeanLocalField.isCompact_closedBall F (ρ ^ j)).isClosed.preimage hcont
    exact hclosedI.inter ((hclosedI.preimage hf).inter h1)
  have hSn : ∀ j, (S j).Nonempty := by
    intro j
    induction j with
    | zero =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hδ
      have hfa : f a = b * Matrix.GeneralLinearGroup.map (τ : F →+* F) a := by
        show x⁻¹ * a⁻¹ * (a * x * b) * _ = _
        group
      have hfaI : f a ∈ iwahori (m := n) F := by
        rw [hfa, ← hUI]
        exact U.mul_mem ((hUI _).2 hb) (hτU _ ((hUI _).2 ha))
      refine ⟨a, ha, hfaI, fun i l _ => ?_⟩
      rw [pow_zero]
      exact mem_unitGL_entries hfaI.1 i l
    | succ j ih =>
      obtain ⟨m, hm, hfm, hD⟩ := ih
      obtain ⟨p, hp, hcU, hcD⟩ := step U hU τ hτ hτU ρ hρ1 hunif e he hc x hx j (f m)
        ((hUI _).2 hfm) hD
      have hfmp : f (m * p) = x⁻¹ * p⁻¹ * x * f m * Matrix.GeneralLinearGroup.map (τ : F →+* F) p := by
        show x⁻¹ * (m * p)⁻¹ * δ * Matrix.GeneralLinearGroup.map (τ : F →+* F) (m * p) =
          x⁻¹ * p⁻¹ * x * (x⁻¹ * m⁻¹ * δ * Matrix.GeneralLinearGroup.map (τ : F →+* F) m) * _
        rw [map_mul]
        group
      refine ⟨m * p, (hUI _).1 (U.mul_mem ((hUI _).2 hm) hp), ?_, ?_⟩
      · rw [hfmp]; exact (hUI _).1 hcU
      · rw [hfmp]; exact hcD
  have hSd : ∀ j, S (j + 1) ⊆ S j := fun j m hm => ⟨hm.1, hm.2.1, fun i l h =>
    (hm.2.2 i l h).trans (pow_le_pow_right_of_le_one' hρ1.le (Nat.le_succ j))⟩
  have hS0 : IsCompact (S 0) := hcpt.of_isClosed_subset (hSc 0) fun m hm => hm.1
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hSd hSn hS0 hSc
  have hm' : ∀ j, m ∈ S j := Set.mem_iInter.1 hm
  have : MulArchimedean (ValueGroupWithZero F) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  refine ⟨m, (hm' 0).1, f m, ⟨(hm' 0).2.1.1, fun i l hil => ?_⟩, ?_⟩
  · by_contra h0
    have hv : valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    obtain ⟨j, hj⟩ := exists_pow_lt₀ hρ1 (Units.mk0 _ hv)
    exact absurd ((hm' j).2.2 i l hil) (not_le.2 hj)
  · show _ = x * (x⁻¹ * m⁻¹ * δ * Matrix.GeneralLinearGroup.map (τ : F →+* F) m)
    group
end GlobalTheory.CompanionTheory.TwContraction
