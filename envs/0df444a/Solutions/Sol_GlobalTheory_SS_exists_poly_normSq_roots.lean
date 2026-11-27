-- Prove2me | solution 1 for GlobalTheory.SS.exists_poly_normSq_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:48:21.807216+00:00
-- url     : https://prove2.me/submissions/ebb0274e-6684-42e0-b2bc-001f160f97d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPositiveDefiniteQuadraticFormEndomorphismsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyTorsionFiniteEndomorphismDivisibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVectorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPolyNormSqRoots
import Theorems.Thm_GlobalTheory_SS_aeval_intertwine
import Theorems.Thm_GlobalTheory_SS_exists_monic_torsion
import Theorems.Thm_GlobalTheory_SS_aeval_ptEnd
import Theorems.Thm_GlobalTheory_T_abelianVariety_torsion_finite_endomorphism_divisible
import Theorems.Thm_GlobalTheory_T_exists_positiveDefinite_quadraticForm_endomorphisms
import Theorems.Thm_GlobalTheory_T_similitude_definite_form_isAlgebraic_on_vector
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
open Polynomial
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ (F : End B) (q : ℕ), IsMonHom (show B ⟶ B from F) → PullPow (show B ⟶ B from F).left L q → ∃ P : Polynomial ℤ, P ≠ 0 ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q) ∧ ∀ x : (𝟙_ (Over (Sp k)) ⟶ B), polyPt F P x = 1 := by
  intro k _ _ B _ hB L hL F q hF hq
  have := hB.comm
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ (l : k) ≠ 0 := by
    by_cases h : ((2 : ℕ) : k) = 0
    · refine ⟨2 + 1, by norm_num, ?_⟩
      rw [Nat.cast_add, h]; simp
    · exact ⟨2, le_rfl, h⟩
  have hD := fun n : ℕ => GlobalTheory.T.abelianVariety_torsion_finite_endomorphism_divisible k B hB (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl)
  obtain ⟨Q, Q1, Q2, Q3, Q4⟩ := GlobalTheory.T.exists_positiveDefinite_quadraticForm_endomorphisms k B hB L hL
  obtain ⟨r, hr⟩ := exists_monic_torsion (M := Additive (𝟙_ (Over (Sp k)) ⟶ B)) l (fun n => (hD n).1) (ptEnd F hF _)
  have hT : ∀ f ∈ homSub B, ptEnd F hF B f ∈ homSub B := fun f hf => by
    change IsMonHom (Additive.toMul f) at hf
    change IsMonHom (Additive.toMul f ≫ (show B ⟶ B from F))
    infer_instance
  let e : homSub B := ⟨Additive.ofMul (𝟙 B), inferInstanceAs (IsMonHom (𝟙 B))⟩
  let φ : Module.End ℤ (homSub B) := (ptEnd F hF B).restrict hT
  have hev : ∀ (x : 𝟙_ (Over (Sp k)) ⟶ B) (p : ℤ[X]), aeval (ptEnd F hF _) p (Additive.ofMul x) =
      Additive.ofMul (x ≫ Additive.toMul (aeval φ p e).1) := fun x p => by
    have h := aeval_intertwine (evalPt x ∘ₗ (homSub B).subtype) φ (ptEnd F hF _)
      (fun f => congrArg Additive.ofMul (Category.assoc x (Additive.toMul f.1) (show B ⟶ B from F))) p e
    have h' : (evalPt x ∘ₗ (homSub B).subtype) e = Additive.ofMul x := congrArg Additive.ofMul (Category.comp_id x)
    rw [h'] at h
    exact h
  obtain ⟨P, hP, h0, hβ⟩ := GlobalTheory.T.similitude_definite_form_isAlgebraic_on_vector (homSub B) (fun f => Q (Additive.toMul f.1)) φ e q l r hl2
    (fun x y => by
      have := Q1 (Additive.toMul x.1) (Additive.toMul y.1)
      rw [sub_eq_add_neg]
      exact this)
    (fun x => Q2 _) (fun x hx => Subtype.ext (Q3 _ x.2 hx)) (fun x => Q4 _ q hq _)
    (fun n => by
      obtain ⟨χ, h1, h2, h3⟩ := hr n
      obtain ⟨g, hg, hg'⟩ := (hD n).2 (Additive.toMul (aeval φ χ e).1) (aeval φ χ e).2 fun x hx =>
        (hev x χ).symm.trans (h3 (Additive.ofMul x) hx)
      exact ⟨χ, ⟨Additive.ofMul g, hg⟩, h1, h2, Subtype.ext hg'⟩)
  refine ⟨P, hP, hβ, fun x => ?_⟩
  have h := (aeval_ptEnd F hF x P).symm.trans (hev x P)
  rw [h0] at h
  exact h.trans (MonObj.comp_one x)
end GlobalTheory.SS
