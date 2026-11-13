-- Prove2me | solution 1 for OAI.Saxl.young_orbit_map_uts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:13:35.881009+00:00
-- url     : https://prove2.me/submissions/949bc58e-d93a-47a7-8faa-f84a96346a41

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_Saxl_orbitAverage_base
import Theorems.Thm_OAI_Saxl_perm_of_equal_content
import Theorems.Thm_OAI_Saxl_vector_of_invariant_functional_uts
import Theorems.Thm_OAI_Saxl_young_invariant_functional_uts

section
-- module Solutions.OAIQ259_US.Saxl_CyclicTensor
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl

theorem young_orbit_map_uts_oai {n : ℕ} (θ τ : YoungDiagram) (t : Tableau n τ)
    (hc : τ.card = θ.card) (hd : Dominates τ θ)
    (w : Fin n → Fin (θ.colLen 0)) (e : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j) :
    ∃ F : Representation.IntertwiningMap (wordRep n (θ.colLen 0)) (spechtRep t),
      F (Pi.single w 1) ≠ 0 := by
  classical
  have hn : τ.card = n := by
    have hh := Fintype.card_congr t
    simpa using hh.symm
  subst n
  obtain ⟨a,l,hl,hac,hle⟩ := young_invariant_functional_uts θ τ hc hd
  obtain ⟨y,hy,hye⟩ := vector_of_invariant_functional_uts (shapeTableau τ) a l hl hle
  let a' := e ∘ a
  have ha' : ∀ g : Equiv.Perm (Fin τ.card), a' ∘ g = a' →
      spechtRep (shapeTableau τ) g y = y := by
    intro g hg
    apply hye g
    funext i
    exact e.injective (congrFun hg i)
  let F := orbitAverage (spechtRep (shapeTableau τ)) a' y
  have hF : F (Pi.single a' 1) ≠ 0 := by
    rw [show F (Pi.single a' 1) = _ from orbitAverage_base _ a' y ha']
    apply smul_ne_zero _ hy
    apply Nat.cast_ne_zero.mpr
    exact Finset.card_ne_zero.mpr ⟨1, by simp⟩
  have hcnt (j : Fin (θ.colLen 0)) :
      (Finset.univ.filter (fun i => w i = j)).card =
        (Finset.univ.filter (fun i => a' i = j)).card := by
    have haeq : Finset.univ.filter (fun i => a' i = j) =
        Finset.univ.filter (fun i => a i = e.symm j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact e.eq_symm_apply.symm
    rw [haeq, hac]
    simpa only [Equiv.apply_symm_apply] using hw (e.symm j)
  obtain ⟨g,hg⟩ := perm_of_equal_content w a' hcnt
  have hwF : F (Pi.single w 1) ≠ 0 := by
    have hw' : Pi.single w (1:ℂ) = wordRep τ.card (θ.colLen 0) g⁻¹ (Pi.single a' 1) := by
      rw [wordRep_single, inv_inv, hg]
    rw [hw', F.isIntertwining]
    intro hz
    apply hF
    have hh := congrArg (spechtRep (shapeTableau τ) g) hz
    rw [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at hh
    exact hh
  let E := equivOfSubrepEq (spechtSub (shapeTableau τ)) (spechtSub t)
    (spechtSub_tableau_independent _ _)
  refine ⟨E.toIntertwiningMap.comp F, ?_⟩
  intro hz
  exact hwF (E.injective (hz.trans (map_zero _).symm))



end Saxl

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.young_orbit_map_uts_oai := @OAI.Saxl.young_orbit_map_uts_oai
