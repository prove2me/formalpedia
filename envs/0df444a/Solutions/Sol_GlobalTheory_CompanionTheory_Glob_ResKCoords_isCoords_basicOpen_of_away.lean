-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:03.64979+00:00
-- url     : https://prove2.me/submissions/52bf9dda-6636-4fd9-a59f-3e788d9f9e8f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisOnLocalizationAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob GlobalTheory.CompanionTheory.Glob.ResKCoords
namespace GlobalTheory.CompanionTheory.Glob.ResKCoords
theorem _root_.solution :
    ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ}
      (x : Fin n → Γ(Y, U.1)),
      (letI := secAlgebra g U.1;
        ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B]
          [IsLocalization.Away s B],
          LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧
            Submodule.span B (Set.range fun i =>
              KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) →
        IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  intro K _ Y g U s n x h
  letI aU : Algebra K Γ(Y, U.1) := secAlgebra g U.1
  letI aB : Algebra K Γ(Y, Y.basicOpen s) := secAlgebra g (Y.basicOpen s)
  letI aUB : Algebra Γ(Y, U.1) Γ(Y, Y.basicOpen s) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom.toAlgebra
  haveI tower : IsScalarTower K Γ(Y, U.1) Γ(Y, Y.basicOpen s) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial)).hom = _
    have e : g.appLE ⊤ U.1 (fun _ _ => trivial) ≫ Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op =
        g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial) := by
      exact Scheme.Hom.appLE_map _ _ _
    rw [← e]
    rfl
  haveI loc : IsLocalization.Away s Γ(Y, Y.basicOpen s) := U.2.isLocalization_basicOpen s
  exact h Γ(Y, Y.basicOpen s)
end GlobalTheory.CompanionTheory.Glob.ResKCoords
