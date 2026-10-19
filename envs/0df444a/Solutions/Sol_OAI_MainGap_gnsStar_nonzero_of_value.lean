-- Prove2me | solution 1 for OAI.MainGap.gnsStar_nonzero_of_value
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:02:11.928503+00:00
-- url     : https://prove2.me/submissions/4e93e3fd-3f7a-4e06-a4d0-5cd61b5414fc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Representation.lean:L79-L95
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.gnsStar_nonzero_of_value. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Representation ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

section Ultra
variable {ι : Type*} (ω : Ultrafilter ι)

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
variable (f : ι → A →ₚ[ℂ] ℂ) (hf : ∀ i a, ‖f i a‖ ≤ ‖a‖)

end Ultra

section GNS
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

lemma gnsStar_nonzero_of_value {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] (g : B →ₚ[ℂ] ℂ) (a : B)
    (ha : g (star a * a) ≠ 0) : g.gnsStarAlgHom a ≠ 0 := by
  intro h
  have hx := congrArg (fun T : g.GNS →L[ℂ] g.GNS => T
    (↑(g.toPreGNS 1) : g.GNS)) h
  have hn := congrArg norm hx
  change ‖g.gnsNonUnitalStarAlgHom a (↑(g.toPreGNS 1) : g.GNS)‖ = ‖(0 : g.GNS)‖ at hn
  rw [g.gnsNonUnitalStarAlgHom_apply_coe, UniformSpace.Completion.norm_coe] at hn
  have hab : ‖g.toPreGNS a‖ = 0 := by
    simp only [norm_zero] at hn
    change ‖g.toPreGNS (a * 1)‖ = 0 at hn
    simpa using hn
  have hh := g.preGNS_norm_sq (g.toPreGNS a)
  rw [hab] at hh
  apply ha
  simpa using hh.symm
end GNS

section Vector
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

end Vector

section LimitRep
variable {ι A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]
variable (ω : Ultrafilter ι) (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))
  (ξ : ∀ i, H i) (hξ : ∀ i, ‖ξ i‖ ≤ 1)

end LimitRep
end MainGap

noncomputable section
open scoped Topology ComplexOrder InnerProductSpace
namespace MainGap

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : A)

end MainGap

end
end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.gnsStar_nonzero_of_value := @_root_.OAI.MainGap.gnsStar_nonzero_of_value
