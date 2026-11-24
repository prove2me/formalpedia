-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.nb_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:44.297372+00:00
-- url     : https://prove2.me/submissions/1875f945-b3a5-41cd-9eb9-3f55935f748f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_smul_le_iff
import Theorems.Thm_GlobalTheory_SW_Nbr_mem_Nb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P)
    {h g : Matrix (Fin n) (Fin n) E} (hh : ∀ x y, herm 1 (h *ᵥ x) (h *ᵥ y) = herm 1 x y)
    (hg : h * g = 1) {Λ Λ₁ Λ' Λ₁' : Lt E n} (h₁ : Λ₁ ∈ Vset E n M) (hm : Moves h Λ Λ₁)
    (hm' : Moves h Λ' Λ₁') (h' : Λ' ∈ Nb M P Λ) : Λ₁' ∈ Nb M P Λ₁ := by
  have hs : ∀ x : Fin n → E, ∃ y, h *ᵥ y = x := fun x =>
    ⟨g *ᵥ x, by rw [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]⟩
  have hS' : SD Λ' := h'.1.2.1
  refine (mem_Nb hP h₁).2 ⟨fun x => ?_, smul_le_iff.2 fun c hc x hx => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hs x
    rw [← hm', hS']
    constructor
    · intro H y hy
      obtain ⟨y, rfl⟩ := hs y
      unfold Int'
      rw [hh]
      exact H y ((hm' y).2 hy)
    · intro H y hy
      have := H _ ((hm' y).1 hy)
      unfold Int' at this ⊢
      rwa [hh] at this
  · obtain ⟨x, rfl⟩ := hs x
    rw [osmul, ← Matrix.mulVec_smul, ← hm']
    exact smul_le_iff.1 h'.2.1 c hc x ((hm x).2 hx)
  · let φ : (Fin n → E) →+ (Fin n → E) := (Matrix.mulVecLin h).toAddMonoidHom
    have e1 : Λ'.toAddSubgroup = Λ₁'.toAddSubgroup.comap φ := AddSubgroup.ext hm'
    have e2 : Λ.toAddSubgroup = Λ₁.toAddSubgroup.comap φ := AddSubgroup.ext hm
    rw [← hP.2.2.1, ← h'.2.2, e1, e2, AddSubgroup.relIndex_comap,
      AddSubgroup.map_comap_eq_self_of_surjective (f := φ) hs]
end GlobalTheory.SW.Nbr
