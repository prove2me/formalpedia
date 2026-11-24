-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.isDiff_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:04:51.155975+00:00
-- url     : https://prove2.me/submissions/5145c279-4e8d-433d-8ec3-ef699678fd7f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_TangentOrigin_evalPt_res
import Theorems.Thm_GlobalTheory_TangentOrigin_jet_res
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_mem_iff
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.TangentOrigin
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
variable {u}
namespace GlobalTheory.TangentOrigin
theorem _root_.solution {v : epsR ℂ ⟶ A} (hv : IsTangent v) {U : A.left.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (w : Fin g → ℂ) :
    u.IsDiff w v ↔ evalPt (R := DualNumber ℂ) v.left U h = jet u w U h0 := by
  constructor
  · intro hd
    refine RingHom.ext fun f => TrivSqZeroExt.ext (tangent_fst hv h h0 f) (hd U h f)
  · intro he W hW f
    have hW0 := (tangent_mem_iff (u := u) hv W).1 hW
    let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
    have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q =>
      Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
    obtain ⟨s, hsW, hs⟩ := hU.exists_basicOpen_le (V := W)
      ⟨(u.ex 0).left pt, hW0 (Set.mem_univ pt)⟩ (h0 (Set.mem_univ pt))
    have hB0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ A.left.basicOpen s := by
      intro q _
      rw [hsub q]
      exact hs
    have hB := (tangent_mem_iff (u := u) hv _).2 hB0
    have := hU.isLocalization_basicOpen s
    have heq : evalPt (R := DualNumber ℂ) v.left _ hB = jet u w _ hB0 := by
      apply IsLocalization.ringHom_ext (Submonoid.powers s)
      refine RingHom.ext fun b => ?_
      change evalPt (R := DualNumber ℂ) v.left _ hB (resG A.left (A.left.basicOpen_le s) b) =
        jet u w _ hB0 (resG A.left (A.left.basicOpen_le s) b)
      rw [evalPt_res _ _ h, jet_res u w _ h0, he]
    change (evalPt (R := DualNumber ℂ) v.left W hW f).snd = (jet u w W hW0 f).snd
    rw [← evalPt_res _ hsW hW hB, ← jet_res u w hsW hW0 hB0, heq]
end GlobalTheory.TangentOrigin
