-- Prove2me | solution 1 for GlobalTheory.HL.Glue.exists_nat_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:05:18.723415+00:00
-- url     : https://prove2.me/submissions/c3087f3e-a9cc-42dd-a27e-ad1ada5d4539

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNatMulMemIntegersQuadraticCompletion
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_P2M_GlobalTheory_HL_Glue__E_mem_8736254c8d80
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Glue
namespace GlobalTheory.HL.Glue
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig)
    (happ : ∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite →
      ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = o)
    (p : HeightOneSpectrum (𝓞 F)) (y : (A.loc p).Ep) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O := by
  set Y : ∀ q, (A.loc q).Ep := Pi.single (M := fun q => (A.loc q).Ep) p y with hY
  have hfin : {q | Y q ∉ (A.L q).O}.Finite := by
    refine (Set.finite_singleton p).subset fun q hq => ?_
    by_contra hne
    apply hq
    simp only [hY]
    rw [Pi.single_eq_of_ne (Set.mem_singleton_iff.not.1 hne)]
    exact (A.L q).O.zero_mem
  obtain ⟨x, hx⟩ := happ Y hfin
  obtain ⟨o, ho, hxo⟩ := hx p
  have hYp : Y p = y := by simp [hY]
  rw [hYp] at hxo
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := halg.exists_integral_multiple
  refine ⟨d.natAbs, Int.natAbs_ne_zero.2 hd0, ?_⟩
  have hint : IsIntegral ℤ ((d.natAbs : E) * x) := by
    rcases Int.natAbs_eq d with h | h
    · have : ((d.natAbs : E) * x) = d • x := by
        rw [zsmul_eq_mul]; congr 1
        exact (Int.cast_natCast (R := E) d.natAbs).symm.trans (congrArg _ h.symm)
      rw [this]; exact hd
    · have : ((d.natAbs : E) * x) = -(d • x) := by
        rw [zsmul_eq_mul, ← neg_mul]; congr 1
        have h' := congrArg (Int.cast (R := E)) h
        rw [h', Int.cast_neg, Int.cast_natCast, neg_neg]
      rw [this]; exact hd.neg
  have h1 := ιE_mem A p _ hint
  have hy : (d.natAbs : (A.loc p).Ep) * y =
      (A.loc p).ιE ((d.natAbs : E) * x) - (d.natAbs : (A.loc p).Ep) * o := by
    rw [map_mul, map_natCast, ← hxo]; ring
  rw [hy]
  exact (A.L p).O.sub_mem h1 ((A.L p).O.mul_mem (natCast_mem (A.L p).O _) ho)
end GlobalTheory.HL.Glue
