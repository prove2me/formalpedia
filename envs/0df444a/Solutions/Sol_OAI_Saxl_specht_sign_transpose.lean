-- Prove2me | solution 1 for OAI.Saxl.specht_sign_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:43:39.262473+00:00
-- url     : https://prove2.me/submissions/1cf8ae95-36e6-4790-9396-d9c9880d41eb

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/SignEquivalence.lean:L91-L150
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.specht_sign_transpose. The node keeps its source
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
import Theorems.Thm_OAI_Saxl_polytabloid_rowWord
import Theorems.Thm_OAI_Saxl_signTwist_irreducible
import Theorems.Thm_OAI_Saxl_specht_irreducible

-- ---- from OAI.RepresentationTheory.Saxl.Polytabloid ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- A finite set is the unique maximizer of its strictly signed separator.
Used below for the Ferrers equality case in the Specht submodule theorem. -/
/- A column-injective rearrangement of the canonical row word has precisely
Ferrers support. This is the equality-of-margins argument, without using
unproved Specht or Young-rule inputs. -/
/- The complex-valued sign character. -/
/- Actual column antisymmetrizer on the word-coordinate module. -/
lemma columnAlt_row {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    columnAlt t (Pi.single (rowWord t) 1) = polytabloid t := by
  simp [columnAlt, polytabloid, LinearMap.sum_apply]

/- Construction of the witnessing column rearrangement. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.HighProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/
/- Local same-high projection in the ordinary pair-letter coordinate space. -/
lemma columnAlt_left {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    wordRep n d (h : Equiv.Perm (Fin n)) * columnAlt (d := d) t =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((h * g : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((h * g : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  rw [← mul_assoc, signC_mul_self, one_mul]

lemma polytabloid_alternating {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) : wordRep n (μ.colLen 0) (h : Equiv.Perm (Fin n))
      (polytabloid t) = signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  rw [← columnAlt_row]
  exact congrArg (fun L : Module.End ℂ (WordSpace n (μ.colLen 0)) =>
    L (Pi.single (rowWord t) 1)) (columnAlt_left t h)

/- Move low row letters to the band and high row letters to B_h. -/
/- The projected generator is genuinely nonzero for every band width,
without assuming a tensor factorization. -/
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
theorem specht_sign_transpose {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Nonempty ((spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) := by
  classical
  let tt := transposeTableau t
  let y : Specht tt := ⟨polytabloid tt, mem_cyclic _ _⟩
  let R := signTwist (spechtRep tt)
  let F := orbitAverage R (rowWord t) y
  let c : ℂ := ((Finset.univ.filter
    (fun g : Equiv.Perm (Fin n) => rowWord t ∘ g = rowWord t)).card : ℂ)
  have hy : ∀ g : Equiv.Perm (Fin n), rowWord t ∘ g = rowWord t → R g y = y := by
    intro g hg
    have hc : g ∈ columnGroup tt := by
      intro i
      exact congrArg Fin.val (congrFun hg i)
    apply Subtype.ext
    change signC g • wordRep n (μ.transpose.colLen 0) g (polytabloid tt) = polytabloid tt
    rw [polytabloid_alternating tt ⟨g, hc⟩, smul_smul, signC_mul_self, one_smul]
  have hF : F (Pi.single (rowWord t) 1) = c • y := orbitAverage_base R _ y hy
  have hc0 : c ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply Finset.card_ne_zero.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rfl
  have hm (g : columnGroup t) :
      (F (wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n))
        (Pi.single (rowWord t) 1))).val (rowWord tt) = signC (g : Equiv.Perm (Fin n)) * c := by
    rw [F.isIntertwining, hF]
    change signC (g : Equiv.Perm (Fin n)) * (c *
      polytabloid tt (rowWord tt ∘ (g : Equiv.Perm (Fin n)))) = _
    have he : rowWord tt ∘ (g : Equiv.Perm (Fin n)) = rowWord tt := by
      funext i
      apply Fin.ext
      exact g.property i
    rw [he, polytabloid_rowWord, mul_one]
  let inc : Representation.IntertwiningMap (spechtRep t) (wordRep n (μ.colLen 0)) :=
    { toLinearMap := (spechtSub t).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let f := F.comp inc
  have hf : f ≠ 0 := by
    intro hz
    have he : (F (polytabloid t)).val (rowWord tt) = 0 := by
      have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) R =>
        (l ⟨polytabloid t, mem_cyclic _ _⟩).val (rowWord tt)) hz
      exact he
    let := Fintype.ofFinite (columnGroup t)
    have hp : (F (polytabloid t)).val (rowWord tt) =
        (Fintype.card (columnGroup t) : ℂ) * c := by
      change (F (∑ g : columnGroup t, signC (g : Equiv.Perm (Fin n)) •
        wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1))).val _ = _
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm]
      simp only [← mul_assoc, signC_mul_self, one_mul, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_ne_zero hn hc0) (hp.symm.trans he)
  let := specht_irreducible t
  let := specht_irreducible tt
  let := signTwist_irreducible (spechtRep tt)
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩
end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.specht_sign_transpose := @_root_.OAI.Saxl.specht_sign_transpose
