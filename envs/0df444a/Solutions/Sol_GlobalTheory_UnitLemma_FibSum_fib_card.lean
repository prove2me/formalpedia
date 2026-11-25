-- Prove2me | solution 1 for GlobalTheory.UnitLemma.FibSum.fib_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:18:39.285839+00:00
-- url     : https://prove2.me/submissions/4cc67743-c139-4812-9c1d-3485dea62241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardSigmaStableProdLatticeExtSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LieLatticeProdComapInlAndMapSndStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeProdOfComapInlMapSndStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumStableLatticesProductEqQPowMul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_card_sigma_stable_prod_lattice_ext_sq
import Theorems.Thm_GlobalTheory_T_card_stable_lattices_alt
import Theorems.Thm_GlobalTheory_T_isFullLattice_prod_of_comap_inl_map_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.FibSum
namespace GlobalTheory.UnitLemma.FibSum
theorem _root_.solution (K : UQ) (B₁ B₂ : InvAlg K) (hg₁ : B₁.σ B₁.g = B₁.g) (hg₂ : B₂.σ B₂.g = B₂.g)
    (hres : resultant B₁.P B₂.P ≠ 0)
    (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A) (h₁ : M₁ ∈ B₁.Lin) (h₂ : M₂ ∈ B₂.Lin) :
    (Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ) =
      (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) := by
  have hI := GlobalTheory.T.card_stable_lattices_alt K.O K.E B₁.A B₂.A B₁.g B₂.g hres M₁ M₂ h₁.1 h₂.1 h₁.2.1 h₂.2.1
  have hH := GlobalTheory.T.card_sigma_stable_prod_lattice_ext_sq K B₁ B₂ hg₁ hg₂ M₁ M₂ h₁ h₂
  have e : {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ≃
      {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} :=
    { toFun := fun M => ⟨M.1, ⟨M.2.1.2.1, M.2.1.2.2⟩, M.2.2⟩
      invFun := fun M => ⟨M.1, ⟨GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd K B₁ B₂ M.1 (by rw [M.2.2.1]; exact h₁.1)
          (by rw [M.2.2.2]; exact h₂.1), M.2.1.1, M.2.1.2⟩, M.2.2⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  rw [Nat.card_congr e]
  have hq2 : (Nat.card (IsLocalRing.ResidueField K.O) : ℚ) = (K.q : ℚ) ^ 2 := by
    rw [K.card_res]; push_cast; ring
  rw [hq2] at hI
  have hqpos : (0 : ℚ) < K.q := by
    have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
    rw [K.card_res] at this
    exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
  have hsq : ((Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ)) ^ 2 =
      ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
    have hpw : ((K.q : ℚ) ^ 2) ^ val K.O (resultant B₁.P B₂.P) = ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have hP₁ : (LinearMap.mulLeft K.E B₁.g).charpoly = B₁.P := rfl
    have hP₂ : (LinearMap.mulLeft K.E B₂.g).charpoly = B₂.P := rfl
    rw [hP₁, hP₂, hpw] at hI
    rw [← hI]
    exact_mod_cast hH
  exact (pow_left_inj₀ (by positivity) (zpow_pos hqpos _).le two_ne_zero).1 hsq
end GlobalTheory.UnitLemma.FibSum
