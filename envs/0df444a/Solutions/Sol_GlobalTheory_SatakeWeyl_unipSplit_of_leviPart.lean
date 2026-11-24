-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.unipSplit_of_leviPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:06:49.317401+00:00
-- url     : https://prove2.me/submissions/7ef0a402-db12-4e73-9c5a-0422b9d87a67

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryUnipotentRadicalSplittingOfLeviPart
import Theorems.Thm_GlobalTheory_SatakeWeyl_exists_mat_submatrix
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution (hL : LeviPart) : UnipSplit := by
  intro L _ _ σ n r e β γ ι hB hι u hu
  obtain ⟨hmono, hrev, hβ, hβrev, hβe, hγ⟩ := hB
  have hu' : ∀ i j : Fin n, j.val ≤ i.val → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j := hu
  have htri : (mat u).BlockTriangular β := by
    intro a b hab
    have hba : b < a := hβ.reflect_lt hab
    rw [hu' a b hba.le, Matrix.one_apply_ne hba.ne']
  obtain ⟨m, hmL, hmu, hrad⟩ := hL L σ n β hβrev u htri
  have hmL' : ∀ i j, β i ≠ β j → mat m i j = 0 := hmL
  have hm : ∀ a b, (a ∉ Set.range e ∨ b ∉ Set.range e) → mat m a b = (1 : Matrix (Fin n) (Fin n) L) a b := by
    intro a b hab
    by_cases h : β a = β b
    · rcases hβe a b h with rfl | ⟨h1, h2⟩
      · rw [hmu a a rfl, hu' a a le_rfl]
      · rcases hab with h' | h'
        · exact absurd h1 h'
        · exact absurd h2 h'
    · rw [hmL' a b h, Matrix.one_apply_ne (fun e' : a = b => h (congrArg β e'))]
  obtain ⟨a, ha⟩ := exists_mat_submatrix e hmono.injective hrev m hm
  have hιa : ι a = m := by
    apply mat_injective
    ext x y
    by_cases hxy : x ∉ Set.range e ∨ y ∉ Set.range e
    · rw [(hι a).2 x y hxy, hm x y hxy]
    · push Not at hxy
      obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hxy
      rw [(hι a).1 i j, ha, Matrix.submatrix_apply]
  refine ⟨a, ⟨?_, ?_⟩, m⁻¹ * u, hrad, by rw [hιa, mul_inv_cancel_left]⟩
  · intro i j hij
    have hij' : j ≤ i := hij
    rw [ha, Matrix.submatrix_apply]
    by_cases h : β (e i) = β (e j)
    · rw [hmu _ _ h, hu' _ _ (hmono.monotone hij'), Matrix.one_apply, Matrix.one_apply]
      simp only [hmono.injective.eq_iff]
    · rw [hmL' _ _ h, Matrix.one_apply_ne (fun e' : i = j => h (by rw [e']))]
  · intro i j hij
    rw [ha, Matrix.submatrix_apply]
    exact hmL' _ _ fun h => hij ((hγ i j).1 h)
end GlobalTheory.SatakeWeyl
