-- Prove2me | solution 1 for OAI.Saxl.young_orbit_map
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:09:41.939482+00:00
-- url     : https://prove2.me/submissions/3726725e-f4b5-4ac9-a671-c77b2fc66b37

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/CyclicTensor.lean:L20-L70
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.young_orbit_map. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Theorems.Thm_OAI_Saxl_vector_of_invariant_functional
import Theorems.Thm_OAI_Saxl_young_invariant_functional

-- ---- from OAI.RepresentationTheory.Saxl.TableauTransport ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A change of tableau enumeration only applies a position permutation. -/
lemma spechtSub_tableau_independent {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    spechtSub s = spechtSub t := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr (polytabloid_mem_all t s)
  · exact (cyclic_le _ _ _).mpr (polytabloid_mem_all s t)
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.SignEquivalence ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

/- Twisting by the actual sign character, on the same complex vector space. -/
lemma orbitAverage_base {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (a : Fin n → Fin d) (y : V)
    (hy : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ρ g y = y) :
    orbitAverage ρ a y (Pi.single a 1) =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin n) => a ∘ g = a)).card : ℂ) • y := by
  classical
  change (∑ g : Equiv.Perm (Fin n), (Pi.single a (1 : ℂ) : WordSpace n d) (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ g y) = _
  have hi (g : Equiv.Perm (Fin n)) : a ∘ (g⁻¹ : Equiv.Perm (Fin n)) = a ↔ a ∘ g = a := by
    constructor <;> intro hh <;> funext i
    · have he := congrFun hh (g i); simpa using he.symm
    · have he := congrFun hh (g⁻¹ i); simpa using he.symm
  simp only [Pi.single_apply, hi]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_congr rfl (fun g hg => hy g (Finset.mem_filter.mp hg).2)]
  simp [Nat.cast_smul_eq_nsmul]

end Saxl

namespace Saxl
/- Sign-conjugacy proved using the column-antisymmetrized row tabloids. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.YoungRule ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Horizontal-strip chains recording the exact ordered strip sizes. -/
/- The actual constructive sufficiency step in Young's rule. No tableau,
Pieri, or representation hypothesis is assumed by this combinatorial theorem. -/
lemma perm_of_equal_content {n d : ℕ} (a b : Fin n → Fin d)
    (h : ∀ j, (Finset.univ.filter (fun i => a i = j)).card =
      (Finset.univ.filter (fun i => b i = j)).card) :
    ∃ g : Equiv.Perm (Fin n), b ∘ g = a := by
  classical
  let e (j) : {i // a i = j} ≃ {i // b i = j} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype] using h j)
  let g := (Equiv.sigmaFiberEquiv a).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv b))
  refine ⟨g, ?_⟩
  funext i
  exact (e (a i) ⟨i,rfl⟩).property

/- Young's sufficiency in the exact form needed for the repeated-row quotient:
a dominant Specht has a nonzero invariant functional for a word of the
prescribed content. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.CyclicTensor ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl

/- Positive Young rule as a concrete orbit map (including reordered contents). -/
theorem young_orbit_map {n : ℕ} (θ τ : YoungDiagram) (t : Tableau n τ)
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
  obtain ⟨a,l,hl,hac,hle⟩ := young_invariant_functional θ τ hc hd
  obtain ⟨y,hy,hye⟩ := vector_of_invariant_functional (shapeTableau τ) a l hl hle
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

-- [generator] dropped (set where defined): attribute [irreducible] intertwiningLiftSubrep

/- The genuine cyclic module is embedded in the actual staircase Specht square. -/
-- [generator] dropped (set where defined): attribute [irreducible] staircaseToTensor

/- Every Specht type occurs in the specified staircase cyclic module. -/
/- A proof of cyclic support proves the original Kronecker-multiplicity target. -/
end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.young_orbit_map := @_root_.OAI.Saxl.young_orbit_map
