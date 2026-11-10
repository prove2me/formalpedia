-- Prove2me | solution 1 for IntLInfty.Kan.theorem_5_10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T02:22:08.643339+00:00
-- url     : https://prove2.me/submissions/0d6cec10-0f41-426b-a6cc-0bbecbefeed1

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ
import Theorems.Thm_IntLInfty_Kan_integ_isSplitSubmanifold
import Theorems.Thm_IntLInfty_Kan_postnikov_genAlg_delta_closed
import Theorems.Thm_IntLInfty_Kan_isKanFibration_of_fillers
import Theorems.Thm_IntLInfty_Kan_fillers_compose_and_low
import Theorems.Thm_IntLInfty_Kan_fillers_tauLe_tauLt
import Theorems.Thm_IntLInfty_Kan_fillers_tauLt_succ_tauLe

set_option autoImplicit false

open scoped ContDiff

namespace IntLInfty.Kan.A83Root

open IntLInfty.Kan

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

/-- Filler data for `∫_S → ∫_{S'}` at level `m`, horn `j`. -/
def FillerAt (r : ℕ) (δ : LInfty L) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (m : ℕ)
    (j : Fin (m + 2))
    (σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) →
      Amb r S (m + 1)) : Prop :=
  (∀ x, ContDiff ℝ ∞ (σ x)) ∧
  (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m j,
      σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m j (σ x y) = y) ∧
  (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m j x) = x)

theorem K0a (δ : LInfty L) :
    (∀ n i, tauLt δ n i ≤ tauLe δ n i) ∧ (∀ n i, tauLe δ n i ≤ tauLt δ (n + 1) i) :=
  ⟨(postnikov_genAlg_delta_closed L δ).1, (postnikov_genAlg_delta_closed L δ).2.1⟩

theorem hcl_tauLe (δ : LInfty L) (n : ℕ) :
    ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ tauLe δ n i → δ.δ (gen L i ξ) ∈ genAlg L (tauLe δ n) :=
  (postnikov_genAlg_delta_closed L δ).2.2.1 n

theorem hcl_tauLt (δ : LInfty L) (n : ℕ) :
    ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ tauLt δ n i → δ.δ (gen L i ξ) ∈ genAlg L (tauLt δ n) :=
  (postnikov_genAlg_delta_closed L δ).2.2.2.1 n

theorem hcl_top (δ : LInfty L) :
    ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ (⊤ : GenSys L) i → δ.δ (gen L i ξ) ∈ genAlg L ⊤ :=
  fun i ξ _ => (postnikov_genAlg_delta_closed L δ).2.2.2.2 i ξ

theorem integ_split {r : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S) (m : ℕ) :
    IsSplitSubmanifold (integ r δ S m) :=
  integ_isSplitSubmanifold r hr L δ S hcl m

theorem isKanFibration_of_fillerAt {r : ℕ} (hr : 1 ≤ r) (δ : LInfty L) {S S' : GenSys L}
    (h : ∀ i, S' i ≤ S i)
    (hS : ∀ m, IsSplitSubmanifold (integ r δ S m)) (hS' : ∀ m, IsSplitSubmanifold (integ r δ S' m))
    (hF : ∀ m (j : Fin (m + 2)), ∃ σ, FillerAt r δ h m j σ) : IsKanFibration r δ S S' :=
  isKanFibration_of_fillers r hr L δ S S' h hS hS' hF

theorem fillerAt_comp {r : ℕ} (hr : 1 ≤ r) (δ : LInfty L) {S S' S'' : GenSys L}
    (h1 : ∀ i, S' i ≤ S i) (h2 : ∀ i, S'' i ≤ S' i) (h3 : ∀ i, S'' i ≤ S i) (m : ℕ)
    (j : Fin (m + 2)) (hF1 : ∃ σ, FillerAt r δ h1 m j σ) (hF2 : ∃ σ, FillerAt r δ h2 m j σ) :
    ∃ σ, FillerAt r δ h3 m j σ :=
  (fillers_compose_and_low r hr L δ).1 S S' S'' h1 h2 h3 m j hF1 hF2

theorem fillerAt_low {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) {S S' : GenSys L}
    (h : ∀ i, S' i ≤ S i) (hlow : ∀ i, i < m + 1 → S i ≤ S' i)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (hcl' : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S' i → δ.δ (gen L i ξ) ∈ genAlg L S')
    (j : Fin (m + 2)) : ∃ σ, FillerAt r δ h m j σ :=
  (fillers_compose_and_low r hr L δ).2 S S' h m hlow hcl hcl' j

theorem fillerAt_tau {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (n : ℕ)
    (h : ∀ i, tauLt δ n i ≤ tauLe δ n i) (j : Fin (m + 2)) : ∃ σ, FillerAt r δ h m j σ :=
  fillers_tauLe_tauLt r hr L δ n h m j

theorem fillerAt_K2 {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (n : ℕ) (j : Fin (m + 2)) :
    ∃ σ, FillerAt r δ (fun i => (K0a δ).2 n i) m j σ :=
  fillers_tauLt_succ_tauLe r hr L δ n (fun i => (K0a δ).2 n i) m j

theorem hcl_bot' (δ : LInfty L) (i : ℕ) (ξ : Module.Dual ℝ (L i)) (hξ : ξ ∈ (⊥ : GenSys L) i) :
    δ.δ (gen L i ξ) ∈ genAlg L (⊥ : GenSys L) := by
  have e : ξ = 0 := (Submodule.mem_bot ℝ).1 hξ
  subst e
  rw [map_zero, map_zero]
  exact Subalgebra.zero_mem _

theorem tauLt_zero_eq_bot (δ : LInfty L) (t : ℕ) : tauLt δ 0 t = ⊥ := by
  unfold tauLt
  split_ifs with h1 h0
  · exact absurd h1 (Nat.not_lt_zero _)
  · subst h0; rfl
  · rfl

theorem tauLt_zero' (δ : LInfty L) : tauLt δ 0 = (⊥ : GenSys L) :=
  funext fun t => tauLt_zero_eq_bot δ t

theorem fillerAt_congr_right {r m : ℕ} (δ : LInfty L) {S S' S'' : GenSys L} (e : S' = S'')
    (h : ∀ i, S' i ≤ S i) (h' : ∀ i, S'' i ≤ S i) (j : Fin (m + 2))
    (hF : ∃ σ, FillerAt r δ h m j σ) : ∃ σ, FillerAt r δ h' m j σ := by
  subst e
  exact hF

/-- The finite tower `τ≤ₙ → τ<ₙ → τ≤ₙ₋₁ → ⋯ → τ<₀ = ⊥`, level-wise. -/
theorem fillerAt_tower {r : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (m : ℕ) (j : Fin (m + 2)) :
    ∀ n, ∃ σ, FillerAt r δ (fun i => (bot_le : (⊥ : GenSys L) i ≤ tauLe δ n i)) m j σ
  | 0 => fillerAt_congr_right δ (tauLt_zero' δ) ((K0a δ).1 0) _ j
      (fillerAt_tau (m := m) hr δ 0 ((K0a δ).1 0) j)
  | n + 1 => by
    have h1 := fillerAt_tau (m := m) hr δ (n + 1) ((K0a δ).1 (n + 1)) j
    have h2 := fillerAt_K2 (m := m) hr δ n j
    have h3 := fillerAt_tower hr δ m j n
    exact fillerAt_comp hr δ ((K0a δ).1 (n + 1)) (fun _ => bot_le) (fun _ => bot_le) m j h1
      (fillerAt_comp hr δ (fun i => (K0a δ).2 n i) (fun _ => bot_le) (fun _ => bot_le) m j h2 h3)

/-- K1: `∫τ≤ₙL → ∫τ<ₙL` is a Kan fibration. -/
theorem K1 {r : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (n : ℕ) :
    IsKanFibration r δ (tauLe δ n) (tauLt δ n) :=
  isKanFibration_of_fillerAt hr δ ((K0a δ).1 n)
    (fun _ => integ_split hr δ _ (hcl_tauLe δ n) _)
    (fun _ => integ_split hr δ _ (hcl_tauLt δ n) _)
    (fun _ j => fillerAt_tau hr δ n ((K0a δ).1 n) j)

/-- K2: `∫τ<ₙ₊₁L → ∫τ≤ₙL` is a Kan fibration. -/
theorem K2 {r : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (n : ℕ) :
    IsKanFibration r δ (tauLt δ (n + 1)) (tauLe δ n) :=
  isKanFibration_of_fillerAt hr δ (fun i => (K0a δ).2 n i)
    (fun _ => integ_split hr δ _ (hcl_tauLt δ (n + 1)) _)
    (fun _ => integ_split hr δ _ (hcl_tauLe δ n) _)
    (fun _ j => fillerAt_K2 hr δ n j)

/-- K3: `∫L → ∗` is a Kan fibration (compose the tower below level `m + 1`). -/
theorem K3 {r : ℕ} (hr : 1 ≤ r) (δ : LInfty L) : IsKanFibration r δ ⊤ ⊥ :=
  isKanFibration_of_fillerAt hr δ (fun _ => bot_le)
    (fun _ => integ_split hr δ _ (hcl_top δ) _)
    (fun _ => integ_split hr δ _ (hcl_bot' δ) _)
    (fun m j => by
      have hlow : ∀ i, i < m + 1 → (⊤ : GenSys L) i ≤ tauLe δ (m + 1) i := fun i hi => by
        simp [tauLe, hi]
      have h1 := fillerAt_low hr δ (S := ⊤) (S' := tauLe δ (m + 1)) (fun _ => le_top) hlow
        (hcl_top δ) (hcl_tauLe δ (m + 1)) j
      have h2 := fillerAt_tower hr δ m j (m + 1)
      exact fillerAt_comp hr δ (S := ⊤) (S' := tauLe δ (m + 1)) (S'' := ⊥) (fun _ => le_top)
        (fun _ => bot_le) (fun _ => bot_le) m j h1 h2)

end IntLInfty.Kan.A83Root

open IntLInfty.Kan in
theorem solution (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) :
    IsKanFibration r δ ⊤ ⊥ ∧
    (∀ n : ℕ, IsKanFibration r δ (tauLe δ n) (tauLt δ n)) ∧
    (∀ n : ℕ, IsKanFibration r δ (tauLt δ (n + 1)) (tauLe δ n)) := by
  exact ⟨A83Root.K3 hr δ, fun n => A83Root.K1 hr δ n, fun n => A83Root.K2 hr δ n⟩
