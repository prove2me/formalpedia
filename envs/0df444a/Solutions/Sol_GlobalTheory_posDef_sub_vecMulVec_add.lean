-- Prove2me | solution 1 for GlobalTheory.posDef_sub_vecMulVec_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:12.255839+00:00
-- url     : https://prove2.me/submissions/a282b154-43b7-4782-8958-8cfa6281b398

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}
namespace GlobalTheory
theorem _root_.solution {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) (e : Fin g)
    {u : Fin g → ℝ} (hu : u e = 1) {y : ℝ} (hy : 0 < y) :
    (Y - (Y e e)⁻¹ • vecMulVec (fun i => Y i e) (fun i => Y i e) + y • vecMulVec u u).PosDef := by
  have hs : ∀ i j, Y j i = Y i j := fun i j => by simpa using hY.1.apply i j
  have he : 0 < Y e e := hY.diag_pos
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp [vecMulVec_apply, hs i j, mul_comm]
  · set a : ℝ := x ⬝ᵥ fun i => Y i e with ha
    have h1 : Y *ᵥ Pi.single e 1 = fun i => Y i e := by
      ext i
      simp
    have h2 : Pi.single e 1 ⬝ᵥ Y *ᵥ x = a := by
      rw [single_dotProduct]
      simp [ha, mulVec, dotProduct, hs e, mul_comm]
    set x' := x - (a / Y e e) • (Pi.single e 1 : Fin g → ℝ) with hx'
    have h3 : star x ⬝ᵥ (Y - (Y e e)⁻¹ • vecMulVec (fun i => Y i e) (fun i => Y i e) +
        y • vecMulVec u u) *ᵥ x = x' ⬝ᵥ Y *ᵥ x' + y * (x ⬝ᵥ u) ^ 2 := by
      simp only [star_trivial, add_mulVec, sub_mulVec, smul_mulVec, vecMulVec_mulVec, hx',
        mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, h1, h2, single_dotProduct, op_smul_eq_smul, smul_eq_mul,
        dotProduct_comm _ x, ← ha]
      field_simp
      ring
    rw [h3]
    by_cases h0 : x' = 0
    · have h4 : x = (a / Y e e) • (Pi.single e 1 : Fin g → ℝ) := sub_eq_zero.1 h0
      have h5 : a / Y e e ≠ 0 := fun h => hx (by rw [h4, h, zero_smul])
      have h6 : x ⬝ᵥ u = a / Y e e := by
        rw [h4]
        simp [hu]
      rw [h0, h6, zero_dotProduct, zero_add]
      positivity
    · have := hY.dotProduct_mulVec_pos h0
      rw [star_trivial] at this
      positivity
end GlobalTheory
