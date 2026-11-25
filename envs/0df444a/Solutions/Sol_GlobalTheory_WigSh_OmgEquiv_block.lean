-- Prove2me | solution 1 for GlobalTheory.WigSh.OmgEquiv.block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:28.371731+00:00
-- url     : https://prove2.me/submissions/4908e6fb-c5b3-48c9-8103-a444e2d44e44

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_herm_UH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
namespace GlobalTheory.WigSh.OmgEquiv
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}
private lemma hpk_apply_of_outer {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if i.val + l.val = 2 * r + k then 1 else 0 := by
  have := i.isLt
  have := l.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
private lemma herm_hpk_bvec_eq_of_outer (v : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : p.val < r ∨ r + k < p.val) (hpq : p.val + q.val = 2 * r + k) :
    herm (Hpk k r) v (bvec p) = v q := by
  have hs : star (bvec p : Fin (2 * r + k + 1) → ℂ) = bvec p := by
    ext j
    by_cases hj : j = p
    · subst hj
      simp [Formalism.QuantumDeterminants.bvec]
    · simp [Formalism.QuantumDeterminants.bvec, hj]
  unfold Formalism.QuantumDeterminants.herm
  rw [hs]
  unfold Formalism.QuantumDeterminants.bvec
  rw [single_dotProduct, one_mul]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single q]
  · rw [hpk_apply_of_outer hp, if_pos hpq, one_mul]
  · intro l _ hl
    rw [hpk_apply_of_outer hp, if_neg, zero_mul]
    intro e
    exact hl (Fin.ext (by omega))
  · intro h
    exact absurd (Finset.mem_univ _) h
end GlobalTheory.WigSh.OmgEquiv
namespace GlobalTheory.WigSh
open OmgEquiv
end GlobalTheory.WigSh
end
end

set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.OmgEquiv
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}
namespace GlobalTheory.WigSh.OmgEquiv
theorem _root_.solution {h : Mx k r} (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1))
    (hij : ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k))) :
    h i j = if i = j then 1 else 0 := by
  have hh' := hh
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hh'
  obtain ⟨hU, hb, -⟩ := hh'
  have hcol : ∀ i j : Fin (2 * r + k + 1), (h *ᵥ bvec j) i = h i j := by
    intro i j
    simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hbv : ∀ i j : Fin (2 * r + k + 1), bvec j i = if i = j then (1 : ℂ) else 0 := by
    intro i j
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]
  have hfix : ∀ p : Fin (2 * r + k + 1), (p.val < r ∨ r + k < p.val) → h *ᵥ bvec p = bvec p := by
    intro p hp
    have := p.isLt
    rcases hp with hp | hp
    · have hq := (hb ⟨p.val, hp⟩).1
      rwa [show eI k r ⟨p.val, hp⟩ = p from Fin.ext rfl] at hq
    · have hp' : 2 * r + k - p.val < r := by omega
      have hq := (hb ⟨2 * r + k - p.val, hp'⟩).2
      rwa [show esI k r ⟨2 * r + k - p.val, hp'⟩ = p from
        Fin.ext (show 2 * r + k - (2 * r + k - p.val) = p.val by omega)] at hq
  have := i.isLt
  have := j.isLt
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [← hcol, hfix j hj, hbv]
  · have hi : i.val < r ∨ r + k < i.val := by
      by_contra hc
      exact hij ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    have hlt : 2 * r + k - i.val < 2 * r + k + 1 := by omega
    have hp : 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val := by omega
    have hpi : 2 * r + k - i.val + i.val = 2 * r + k := by omega
    calc h i j = (h *ᵥ bvec j) i := (hcol i j).symm
      _ = herm (Hpk k r) (h *ᵥ bvec j) (bvec ⟨2 * r + k - i.val, hlt⟩) :=
          (herm_hpk_bvec_eq_of_outer _ ⟨2 * r + k - i.val, hlt⟩ i hp hpi).symm
      _ = herm (Hpk k r) (h *ᵥ bvec j) (h *ᵥ bvec ⟨2 * r + k - i.val, hlt⟩) := by
          rw [hfix ⟨2 * r + k - i.val, hlt⟩ hp]
      _ = herm (Hpk k r) (bvec j) (bvec ⟨2 * r + k - i.val, hlt⟩) :=
          GlobalTheory.WigSh.OmgEquiv.herm_UH hU _ _
      _ = bvec j i := herm_hpk_bvec_eq_of_outer _ ⟨2 * r + k - i.val, hlt⟩ i hp hpi
      _ = if i = j then 1 else 0 := hbv i j
end GlobalTheory.WigSh.OmgEquiv
