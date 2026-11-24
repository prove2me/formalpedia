-- Prove2me | solution 1 for GlobalTheory.BCT.SuppFin.gl_entries_bounded_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:27:42.365453+00:00
-- url     : https://prove2.me/submissions/343fe107-2a09-4b45-a84b-1f34ea8186b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlAdicCompletionEntriesBoundedOfIsCompact
import Theorems.Thm_GlobalTheory_BCT_SuppFin_exists_bound_of_isCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
noncomputable section
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.SuppFin
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.BCT.SuppFin
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (D : Set (GL (Fin n) (w.adicCompletion E))),
    IsCompact D → ∃ N : ℤ, ∀ h ∈ D, ∀ i j,
      Valued.v (h.val i j) ≤ WithZero.exp N ∧ Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by
  intro E _ _ w n D hD
  have h1 : ∀ i j, ∃ N : ℤ, ∀ h ∈ D, Valued.v (h.val i j) ≤ WithZero.exp N := by
    intro i j
    obtain ⟨N, hN⟩ := exists_bound_of_isCompact w
      (hD.image (Units.continuous_val.matrix_elem i j))
    exact ⟨N, fun h hh => hN _ ⟨h, hh, rfl⟩⟩
  have h2 : ∀ i j, ∃ N : ℤ, ∀ h ∈ D, Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by
    intro i j
    obtain ⟨N, hN⟩ := exists_bound_of_isCompact w
      (hD.image ((Units.continuous_coe_inv).matrix_elem i j))
    exact ⟨N, fun h hh => hN _ ⟨h, hh, rfl⟩⟩
  choose N1 hN1 using h1
  choose N2 hN2 using h2
  refine ⟨((Finset.univ.sup (fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) : ℕ) : ℤ) ⊔
      ((Finset.univ.sup (fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) : ℕ) : ℤ), ?_⟩
  intro h hh i j
  have a1 : N1 i j ≤ ((Finset.univ.sup (fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) : ℕ) : ℤ) :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.2
      (Finset.le_sup (f := fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) (Finset.mem_univ (i, j))))
  have a2 : N2 i j ≤ ((Finset.univ.sup (fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) : ℕ) : ℤ) :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.2
      (Finset.le_sup (f := fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) (Finset.mem_univ (i, j))))
  exact ⟨(hN1 i j h hh).trans (WithZero.exp_le_exp.2 (a1.trans le_sup_left)),
    (hN2 i j h hh).trans (WithZero.exp_le_exp.2 (a2.trans le_sup_right))⟩
end GlobalTheory.BCT.SuppFin
