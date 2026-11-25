-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif.IsSec.add_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:53:36.963463+00:00
-- url     : https://prove2.me/submissions/0bc04d63-a43b-4016-b087-f50050555a00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_ExponentialDifferential
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EpsilonPointMorphisms_Exp_exp_add_lat
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EpsilonPointMorphisms_Unif_exists_chart

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms
open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (F : Unif A L g)
namespace GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif
namespace IsSec
theorem _root_.solution {F : Unif A L g} {a : F.toExp.lat → (Fin g → ℂ) → ℂ} (ha : F.HasFactor a) {s : L.Sec}
    {θ : (Fin g → ℂ) → ℂ} (hs : F.IsSec s θ) (la : F.toExp.lat) (z : Fin g → ℂ) :
    θ (z + la) = a la z * θ z := by
  obtain ⟨i, h⟩ := F.exists_chart z
  have e : F.exp (z + la) = F.exp z := F.toExp.exp_add_lat z la
  have h' : z + la ∈ pre F.exp (L.U i) := by
    change In (F.exp (z + la)).mor _
    rw [e]; exact h
  have hv : ∀ (x y : Pt A) (_ : x = y) (hx : In x.mor (L.U i)) (hy : In y.mor (L.U i)),
      val x.mor hx (s.f i) = val y.mor hy (s.f i) := by
    intro x y hxy hx hy; subst hxy; rfl
  have h1 := hs i z h
  have h2 := hs i (z + la) h'
  rw [hv _ _ e h' h, h1, ha la z i h h'] at h2
  apply mul_right_cancel₀ (F.fr_ne i _ h')
  rw [← h2]; ring
end IsSec
end GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif
