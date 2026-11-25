-- Prove2me | solution 1 for GlobalTheory.HL.pattern_strong_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:20:37.092316+00:00
-- url     : https://prove2.me/submissions/a0985ea3-9059-4e86-a992-f92dc83b64b2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PatternUnitriangularStrongApproximation
import Theorems.Thm_GlobalTheory_HL_PatternApprox_exists_clear
import Theorems.Thm_GlobalTheory_HL_PatternApprox_det_eq_one
import Theorems.Thm_GlobalTheory_HL_PatternApprox_adjugate_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_strong_approximation_additive_quadratic_extension
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
open GlobalTheory.HL.PatternApprox
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (m : ℕ) (I : Fin m → Fin m → Prop), (∀ i j, I i j → i < j) → (∀ i j l, I i j → I j l → I i l) → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ s : ∀ p, Matrix (Fin m) (Fin m) (A.loc p).Ep, (∀ p i j, ¬ I i j → s p i j = if i = j then 1 else 0) → {p | ¬ IsIntM (A.L p) (s p)}.Finite → ∃ t : Matrix (Fin m) (Fin m) E, (∀ i j, ¬ I i j → t i j = if i = j then 1 else 0) ∧ ∀ p i j, ∃ o ∈ (A.L p).O, ((s p)⁻¹ * t.map (A.loc p).ιE - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  intro F E _ _ _ _ _ sig A m I hlt _htr c hc s hs hsint
  have hinv : ∀ p, (s p)⁻¹ = (s p).adjugate := fun p => by
    rw [Matrix.inv_def, det_eq_one I hlt (s p) (hs p), Ring.inverse_one, one_smul]
  have hcl : ∀ p, ∃ a : ((A.loc p).Fp)ˣ, (IsIntM (A.L p) (s p) → a = 1) ∧
      ∀ i j, algebraMap (A.loc p).Fp (A.loc p).Ep (a : (A.loc p).Fp) * (s p)⁻¹ i j ∈ (A.L p).O := by
    intro p
    haveI := (A.loc p).lf
    haveI : Module.Free (A.loc p).Fp (A.loc p).Ep := (A.loc p).free
    haveI : Module.Finite (A.loc p).Fp (A.loc p).Ep := Module.finite_of_finrank_eq_succ (A.loc p).rank
    by_cases h : IsIntM (A.L p) (s p)
    · refine ⟨1, fun _ => rfl, fun i j => ?_⟩
      rw [Units.val_one, map_one, one_mul, hinv p]
      exact adjugate_mem (A.L p).O (s p) h i j
    · obtain ⟨a, ha0, ha⟩ := exists_clear (A.L p).O (A.L p).O_def
        (fun ij : Fin m × Fin m => (s p)⁻¹ ij.1 ij.2)
      exact ⟨Units.mk0 a ha0, fun h' => absurd h' h, fun i j => ha (i, j)⟩
  choose c' hc'1 hc'2 using hcl
  let d : ∀ p, ((A.loc p).Fp)ˣ := fun p => c p * c' p
  have hd : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite := by
    apply (hc.union hsint).subset
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    obtain ⟨⟨u, hu⟩, hint⟩ := hno
    exact hp ⟨u, by simp [d, hc'1 p hint, hu]⟩
  have hap := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A d hd).2.1
  have hx : ∀ i j, ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O,
      (A.loc p).ιE x - s p i j = algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o :=
    fun i j => hap (fun p => s p i j) (hsint.subset fun p hp hi => hp (hi i j))
  choose x hx using hx
  refine ⟨fun i j => if I i j then x i j else if i = j then 1 else 0, fun i j h => by simp [h], fun p i j => ?_⟩
  set t : Matrix (Fin m) (Fin m) E := fun i j => if I i j then x i j else if i = j then 1 else 0 with ht
  have hD : ∀ k l, ∃ o ∈ (A.L p).O, (t.map (A.loc p).ιE - s p) k l =
      algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o := by
    intro k l
    by_cases hkl : I k l
    · obtain ⟨o, ho, he⟩ := hx k l p
      refine ⟨o, ho, ?_⟩
      rw [← he]
      show (A.loc p).ιE (t k l) - s p k l = (A.loc p).ιE (x k l) - s p k l
      rw [ht]
      simp only [hkl, if_true]
    · refine ⟨0, (A.L p).O.zero_mem, ?_⟩
      rw [Matrix.sub_apply, Matrix.map_apply, hs p k l hkl, mul_zero]
      simp only [ht, hkl, if_false]
      split_ifs <;> simp
  choose o ho hoeq using hD
  have hunit : (s p)⁻¹ * s p = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [det_eq_one I hlt (s p) (hs p)]; exact isUnit_one)
  have heq : (s p)⁻¹ * t.map (A.loc p).ιE - 1 = (s p)⁻¹ * (t.map (A.loc p).ιE - s p) := by
    rw [Matrix.mul_sub, hunit]
  refine ⟨∑ k, (algebraMap (A.loc p).Fp (A.loc p).Ep (c' p : (A.loc p).Fp) * (s p)⁻¹ i k) * o k j,
    (A.L p).O.sum_mem fun k _ => (A.L p).O.mul_mem (hc'2 p i k) (ho k j), ?_⟩
  rw [heq, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hoeq k j]
  simp only [d, Units.val_mul, map_mul]
  ring
end GlobalTheory.HL
