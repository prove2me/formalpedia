-- Prove2me | solution 1 for OAI.ComplexCancellation.RelativeClearing.uniform
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:02:01.333861+00:00
-- url     : https://prove2.me/submissions/5c14fb91-f6da-4a97-9956-42faf64716fa

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/RelativeClearing.lean:L29-L49
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.RelativeClearing.uniform. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing

-- ---- from OAI.Algebra.AffineCancellation.RelativeClearing ----
namespace OAI

noncomputable section

namespace ComplexCancellation.RelativeClearing
variable {k A B R : Type*} [CommRing k] [CommRing A] [IsDomain A] [CommRing B] [CommRing R]
  [Algebra k A] [Algebra k B] [Algebra k R]
variable (h : A →ₐ[k] B) (f : B →ₐ[k] R) (D : Derivation k A A)
lemma uniform (s : Finset B) (E : Derivation k R R)
    (hc : ∀ b, E (f b) ∈ subalgebra h f D) :
    ∃ c : A, D c=0 ∧ c≠0 ∧ ∀ b∈s, ∃ t : B, f (h c)*E (f b)=f t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,D.map_one_eq_zero,one_ne_zero,by simp⟩
  | @insert b s hbs ih =>
    obtain ⟨c,t,hc,hcn,hct⟩ := hc b
    obtain ⟨d,hd,hdn,hds⟩ := ih
    refine ⟨c*d,?_,mul_ne_zero hcn hdn,?_⟩
    · rw [Derivation.leibniz,hc,hd,smul_zero,smul_zero,add_zero]
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl|ha
      · refine ⟨h d*t,?_⟩
        simp only [map_mul]
        calc f (h c)*f (h d)*E (f a)=f (h d)*(f (h c)*E (f a)) := by ring
          _ = _ := by rw [hct]
      · obtain ⟨u,hu⟩ := hds a ha
        refine ⟨h c*u,?_⟩
        simp only [map_mul]
        rw [mul_assoc,hu]
end ComplexCancellation.RelativeClearing

namespace ComplexCancellation.DerivationRange
variable {k B R : Type*} [CommRing k] [CommRing B] [CommRing R] [Algebra k B] [Algebra k R]
end ComplexCancellation.DerivationRange

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.RelativeClearing


theorem solution : type_of% @_root_.OAI.ComplexCancellation.RelativeClearing.uniform := @_root_.OAI.ComplexCancellation.RelativeClearing.uniform
