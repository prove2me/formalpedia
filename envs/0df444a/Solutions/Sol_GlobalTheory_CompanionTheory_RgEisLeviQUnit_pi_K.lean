-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.pi_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:35.746738+00:00
-- url     : https://prove2.me/submissions/525a65e0-25e0-4538-a3ae-c1d2861ac188

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
  [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ) (hσ : ∀ x, A.σ (A.σ x) = x)
include hσ
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (q : A.uQ ε s) (hq : (q : A.U ε ι) ∈ A.uK ε ι) : piQ A ε hσ q ∈ A.uK ε ↥sᶜ := by
  have h := Subgroup.mem_subgroupOf.1 hq
  refine Subgroup.mem_subgroupOf.2 ⟨fun r c => h.1 (emb s r) (emb s c), fun w => ?_⟩
  have hU := h.2 w
  set g := ((q : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) with hg
  set gi := ((((q : A.U ε ι).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) with hgi
  have hmul : g.map (A.φ w) * gi.map (A.φ w) = 1 := by
    rw [← Matrix.map_mul, hg, hgi, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 := Matrix.mem_unitaryGroup_iff'.1 hU
  have e : gi.map (A.φ w) = star (g.map (A.φ w)) := by
    rw [← Matrix.one_mul (gi.map (A.φ w)), ← h2, Matrix.mul_assoc, hmul, Matrix.mul_one]
  have t1 : Tri s (g.map (A.φ w)) := (q_tri A ε hσ q).map _
  have t2 : Tri s (gi.map (A.φ w)) := (q_tri' A ε hσ q).map _
  have h3 := t1.sub_mul t2
  rw [hmul, Matrix.submatrix_one _ emb_inj, e] at h3
  refine Matrix.mem_unitaryGroup_iff.2 ?_
  exact h3.symm
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
