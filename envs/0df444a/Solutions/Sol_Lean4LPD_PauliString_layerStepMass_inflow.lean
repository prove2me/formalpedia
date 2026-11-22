-- Prove2me | solution 1 for Lean4LPD.PauliString.layerStepMass_inflow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:11:39.294116+00:00
-- url     : https://prove2.me/submissions/63816944-cb60-4ebb-a93f-f15f5ddf0385

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
public import Theorems.Thm_Lean4LPD_PauliString_layerBlockTraj_eq_scheduled_prefix
public import Theorems.Thm_Lean4LPD_entryFactor_nonneg_all


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (layers : ℕ → List (PauliString n × ℝ))
    (Γ : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m : ℕ}
    (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a) (hm : 1 ≤ m)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (d i : ℕ) (hi : i < Γ) :
    layerStepMass layers Γ (rungWeight ko kh m) O d (i + 1) ≤
      layerStepMass layers Γ (rungWeight ko kh m) O d i +
        (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
          layerN (fun T => layers (T % Γ)) (trotterSchedule Γ (rungWeight ko kh m)) O ko kh
            (m - j) (d * Γ + i)) +
        entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a m * pauliNorm O := by
  let A := layerBlockTraj layers (layerStepTraj layers Γ (rungWeight ko kh m) O d) i
  have hA : A = layerScheduledTraj layers Γ (rungWeight ko kh m) O (d * Γ + i) :=
    layerBlockTraj_eq_scheduled_prefix layers Γ _ O d i hi
  have hnorm : pauliNorm A ≤ pauliNorm O := by
    rw [hA]
    exact pauliNorm_layerTraj_le _ (fun T => hherm (T % Γ)) _ O _
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  have hE := entryFactor_nonneg_all hkh1
    (div_nonneg (Nat.cast_nonneg ko) hkh1.le) ha m
  have hflow := highNorm_layerConj_le_multi (layers i) hkh (hL i) (hherm i) ha (hsin i) hm hb A
  have hsum : (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
      highNorm (rungWeight ko kh (m - j)) A) =
      ∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
        layerN (fun T => layers (T % Γ)) (trotterSchedule Γ (rungWeight ko kh m)) O ko kh
          (m - j) (d * Γ + i) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [layerN_eq_highNorm _ _ _ _ _ _ _ (by have := Finset.mem_Ico.1 hj; omega), hA]
    rfl
  rw [hsum] at hflow
  exact hflow.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hnorm hE))
end Lean4LPD.PauliString
