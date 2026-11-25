-- Prove2me | solution 1 for GlobalTheory.HL.LocCongApprox.approx_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:56.928216+00:00
-- url     : https://prove2.me/submissions/46874470-a422-4388-a19d-6db365bda610

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntCastIsUnitCompletionAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsGlobalUnitriangularOfLocalCongruence
import Theorems.Thm_GlobalTheory_HL_PlacesInt_intCast_isUnit_almost_all
import Theorems.Thm_GlobalTheory_HL_PlacesInt_integers_local
import Theorems.Thm_GlobalTheory_HL_StrongApprox_strong_approx_additive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocCongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.LocCongApprox
theorem _root_.solution (A : Places F E sig) (g : ℕ) (hg : 0 < g) (p : HeightOneSpectrum (𝓞 F))
    (z : (A.loc p).Ep) (hz : z ∈ (A.L p).O) :
    ∃ x : 𝓞 E, ∃ o ∈ (A.L p).O, z - (A.loc p).ιE (x : E) = (A.loc p).ιE (g : E) * o := by
  have hgF : ((g : ℤ) : F) ≠ 0 := by exact_mod_cast hg.ne'
  let c : ∀ q, ((A.loc q).Fp)ˣ := fun q => Units.mk0 ((g : ℤ) : (A.loc q).Fp) (by
    rw [← map_intCast (A.loc q).ιF]; exact (map_ne_zero _).2 hgF)
  have hc := PlacesInt.intCast_isUnit_almost_all A (g : ℤ) (by exact_mod_cast hg.ne')
  have hcE : ∀ q, algebraMap (A.loc q).Fp (A.loc q).Ep (c q) = (A.loc q).ιE (g : E) := by
    intro q
    change algebraMap (A.loc q).Fp (A.loc q).Ep ((g : ℤ) : (A.loc q).Fp) = _
    rw [map_intCast, map_natCast, Int.cast_natCast]
  have hgO : ∀ q, (A.loc q).ιE (g : E) ∈ (A.L q).O := fun q => by
    rw [map_natCast]; exact natCast_mem (A.L q).O g
  let y : ∀ q, (A.loc q).Ep := Pi.single (M := fun q => (A.loc q).Ep) p z
  have hy : {q | y q ∉ (A.L q).O}.Finite := by
    refine (Set.finite_singleton p).subset fun q hq => ?_
    by_contra hne
    apply hq
    change Pi.single (M := fun q => (A.loc q).Ep) p z q ∈ (A.L q).O
    rw [Pi.single_eq_of_ne hne]
    exact zero_mem _
  obtain ⟨-, hE, -⟩ := StrongApprox.strong_approx_additive A c hc
  obtain ⟨x, hx⟩ := hE y hy
  have hint : ∀ q, (A.loc q).ιE x ∈ (A.L q).O := by
    intro q
    obtain ⟨o, ho, he⟩ := hx q
    have hyq : y q ∈ (A.L q).O := by
      by_cases h : q = p
      · subst h
        change Pi.single (M := fun q => (A.loc q).Ep) q z q ∈ (A.L q).O
        rw [Pi.single_eq_same]; exact hz
      · change Pi.single (M := fun q => (A.loc q).Ep) p z q ∈ (A.L q).O
        rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have e : (A.loc q).ιE x = y q + algebraMap (A.loc q).Fp (A.loc q).Ep (c q) * o := by
      rw [← he]; ring
    rw [e, hcE]
    exact add_mem hyq (mul_mem (hgO q) ho)
  obtain ⟨xo, hxo⟩ := ((PlacesInt.integers_local A).1 x).1 hint
  obtain ⟨o, ho, he⟩ := hx p
  refine ⟨xo, -o, neg_mem ho, ?_⟩
  have hyp : y p = z := by
    change Pi.single (M := fun q => (A.loc q).Ep) p z p = z
    exact Pi.single_eq_same _ _
  rw [hyp, hcE] at he
  rw [hxo]
  linear_combination -he
end GlobalTheory.HL.LocCongApprox
