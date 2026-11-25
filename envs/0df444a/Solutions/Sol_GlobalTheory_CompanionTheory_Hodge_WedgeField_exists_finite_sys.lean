-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.WedgeField.exists_finite_sys
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:37:09.456721+00:00
-- url     : https://prove2.me/submissions/958b9809-dc93-48bb-a8e9-a2282a8fb6e1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.WedgeField
namespace GlobalTheory.CompanionTheory.Hodge.WedgeField
theorem _root_.solution {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsSeparated s]
    [CompactSpace X] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  have hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (Limits.pullback.diagonal s)) ⊤ (isAffineOpen_top _) U le_top W le_top hU hW
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := fun x _ => by
    have hx : x ∈ (⨆ U : X.affineOpens, U.1 : X.Opens) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact Set.mem_iUnion.2 ⟨U, hU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) hcov
  let A : Set X.Opens := (fun U : X.affineOpens => U.1) '' (t : Set X.affineOpens)
  have hfin : (infClosure A).Finite := (t.finite_toSet.image _).infClosure
  have haff : infClosure A ⊆ {V : X.Opens | IsAffineOpen V} :=
    infClosure_min (by rintro _ ⟨U, _, rfl⟩; exact U.2) fun a ha b hb => hinter a b ha hb
  letI inst : SemilatticeInf (infClosure A) :=
    Subtype.semilatticeInf fun x y hx hy => infClosed_infClosure hx hy
  refine ⟨infClosure A, inst, hfin.to_subtype, ⟨⟨fun p => ⟨p.1, haff p.2⟩, fun a b => rfl, ?_⟩⟩⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨⟨U.1, subset_infClosure ⟨U, hU, rfl⟩⟩, hx⟩
end GlobalTheory.CompanionTheory.Hodge.WedgeField
