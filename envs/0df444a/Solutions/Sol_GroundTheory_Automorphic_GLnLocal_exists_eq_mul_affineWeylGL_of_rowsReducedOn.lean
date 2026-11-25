-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.exists_eq_mul_affineWeylGL_of_rowsReducedOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:00:45.299749+00:00
-- url     : https://prove2.me/submissions/6cf342be-59c3-43d8-9687-b91ecc07112c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_mem_iwahori
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_affineWeylGL_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_valuation_div_zpow_eq_one
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (g : GL (Fin n) F)
    (hred : RowsReducedOn (g : Matrix (Fin n) (Fin n) F) Finset.univ) :
    ∃ w : ExtendedAffineWeyl n, ∃ t ∈ iwahori F n, g = t * affineWeylGL F n w := by
  classical
  obtain ⟨p, hp⟩ := hred
  have hp' := fun i => hp i (Finset.mem_univ i)
  have hinj : Function.Injective p := by
    intro i i' e
    by_contra hii
    exact (hp' i').1 (e ▸ (hp' i).2.2 i' (Ne.symm hii))
  let τ : Equiv.Perm (Fin n) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj)
  have hτ : ∀ i, τ i = p i := fun i => rfl
  choose m hm using fun i => exists_valuation_div_zpow_eq_one F (hp' i).1
  let w : ExtendedAffineWeyl n := ⟨fun i => Multiplicative.ofAdd (m i), τ⁻¹⟩
  let d : Fin n → F := fun i => (g : Matrix (Fin n) (Fin n) F) i (p i) / ϖ ^ m i
  obtain ⟨t, ht, htd⟩ := exists_mem_iwahori F n (diagonal d)
    (fun i j => by
      rw [diagonal_apply]
      split_ifs with hij
      · exact (hm i).le
      · rw [map_zero]
        exact zero_le)
    (fun i j hji => by
      rw [diagonal_apply, if_neg hji.ne', map_zero]
      exact zero_lt_one)
    (fun i => by rw [diagonal_apply_eq]; exact hm i)
  refine ⟨w, t, ht, Units.ext ?_⟩
  ext i j
  rw [Units.val_mul, htd, diagonal_mul, affineWeylGL_apply]
  have hϖm : ϖ ^ m i ≠ 0 := zpow_ne_zero _ (uniformizer_ne_zero F)
  by_cases hj : j = p i
  · subst hj
    rw [if_pos (by simp [w, ← hτ])]
    simp only [d, w, toAdd_ofAdd]
    rw [div_mul_cancel₀ _ hϖm]
  · rw [(hp' i).2.1 j hj, if_neg, mul_zero]
    intro e
    apply hj
    simp only [w] at e
    rw [← hτ, e]
    simp
end GroundTheory.Automorphic.GLnLocal
