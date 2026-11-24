-- Prove2me | solution 1 for GlobalTheory.HeckeOne.exists_trivial_on_expScalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:36.301469+00:00
-- url     : https://prove2.me/submissions/3fc4434a-3f01-4fbe-8a63-f159d6144a75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExtensionEmbeddingMixedSymmOfIsComplex
import Theorems.Thm_GlobalTheory_HeckeOne_exists_eq_circleExp_mul
import Theorems.Thm_GlobalTheory_HeckeOne_continuous_mixedIdele
import Theorems.Thm_GlobalTheory_HeckeOne_expScalar_add
import Theorems.Thm_GlobalTheory_HeckeOne_continuous_expScalar
import Theorems.Thm_GlobalTheory_HeckeOne_ideleNorm_expScalar
import Theorems.Thm_GlobalTheory_HeckeOne_normChar_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
open GlobalTheory GlobalTheory.HeckeOne
variable (K : Type) [Field K] [NumberField K]
variable {K}
namespace GlobalTheory.HeckeOne
theorem _root_.solution (χ : HChar K) (hχ : χ.IsUnitary) :
    ∃ t : ℝ, ∀ x : ℝ, (χ * normChar K (-t)).1 (mixedIdele K (expScalar K x)) = 1 := by
  let f : ℝ → Circle := fun x => ⟨(χ.1 (mixedIdele K (expScalar K x)) : ℂ),
    mem_sphere_zero_iff_norm.2 (hχ _)⟩
  have hf : Continuous f := Continuous.subtype_mk
    (Units.continuous_val.comp (χ.2.1.comp ((continuous_mixedIdele K).comp (continuous_expScalar K)))) _
  obtain ⟨a, ha⟩ := exists_eq_circleExp_mul f hf fun x y => Circle.ext (by
    change (χ.1 (mixedIdele K (expScalar K (x + y))) : ℂ) =
      (χ.1 (mixedIdele K (expScalar K x)) : ℂ) * (χ.1 (mixedIdele K (expScalar K y)) : ℂ)
    rw [expScalar_add, map_mul, map_mul, Units.val_mul])
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  refine ⟨a / Module.finrank ℚ K, fun x => Units.ext ?_⟩
  change (f x : ℂ) * (((normChar K _).1 (mixedIdele K (expScalar K x)) : ℂˣ) : ℂ) = 1
  rw [normChar_apply, ideleNorm_expScalar, Real.log_exp, ha, ← Circle.coe_mul, ← Circle.exp_add]
  have : a * x + -(a / (Module.finrank ℚ K : ℝ)) * ((Module.finrank ℚ K : ℝ) * x) = 0 := by
    field_simp
    ring
  rw [this, Circle.exp_zero, Circle.coe_one]
end GlobalTheory.HeckeOne
