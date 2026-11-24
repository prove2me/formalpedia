-- Prove2me | solution 1 for GlobalTheory.GenericHom.exists_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:05:50.574381+00:00
-- url     : https://prove2.me/submissions/2424ec0b-bf59-41bc-9044-6ec5287bc480

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMonHomExtension
import Theorems.Thm_GlobalTheory_GenericHom_exists_point_mem
import Theorems.Thm_GlobalTheory_GenericHom_exists_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.GenericHom
variable {k : Type} [Field k] [IsAlgClosed k]
namespace GlobalTheory.GenericHom
theorem _root_.solution {U H : Over (Sp k)} [LocallyOfFiniteType H.hom] [IrreducibleSpace H.left]
    (j : U ⟶ H) [IsOpenImmersion j.left] [Nonempty U.left] (s : List (H ≅ H)) :
    ∃ u : 𝟙_ (Over (Sp k)) ⟶ H, ∀ φ ∈ s, ∃ p, p ≫ j = u ≫ φ.hom := by
  have key : ∃ W : Set H.left, IsOpen W ∧ W.Nonempty ∧
      ∀ φ ∈ s, ∀ w ∈ W, φ.hom.left w ∈ Set.range j.left := by
    induction s with
    | nil => exact ⟨Set.univ, isOpen_univ, Set.univ_nonempty, by simp⟩
    | cons φ s ih =>
      obtain ⟨W, h1, h2, h3⟩ := ih
      have ho : IsOpen (φ.hom.left ⁻¹' Set.range j.left) :=
        (IsOpenImmersion.isOpen_range j.left).preimage φ.hom.left.continuous
      have hn : (φ.hom.left ⁻¹' Set.range j.left).Nonempty := by
        obtain ⟨v⟩ := ‹Nonempty U.left›
        refine ⟨φ.inv.left (j.left v), v, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, φ.inv_hom_id]
        rfl
      refine ⟨W ∩ φ.hom.left ⁻¹' Set.range j.left, h1.inter ho,
        nonempty_preirreducible_inter h1 ho h2 hn, ?_⟩
      intro ψ hψ w hw
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact hw.2
      · exact h3 ψ hψ w hw.1
  obtain ⟨W, h1, h2, h3⟩ := key
  obtain ⟨u, hu⟩ := exists_point_mem H W h1.isLocallyClosed h2
  exact ⟨u, fun φ hφ => exists_lift j _ fun p => h3 φ hφ _ (hu p)⟩
end GlobalTheory.GenericHom
