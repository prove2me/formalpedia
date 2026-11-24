-- Prove2me | solution 1 for GlobalTheory.SplitLocComm.commute_of_loc_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:43:30.424851+00:00
-- url     : https://prove2.me/submissions/6bc9e196-4590-40ff-8303-8464f11991fd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCompAtEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRealAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CommuteOfLocEqOne
import Theorems.Thm_GlobalTheory_SplitLocComm_map_compAt_eq_one
import Theorems.Thm_GlobalTheory_AdelicComp_eq_zero_of_compAt_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
noncomputable section
open GlobalTheory GlobalTheory.SplitLocComm
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L
namespace GlobalTheory.SplitLocComm
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (x y : GAf L n), s.loc n x = 1 → TrivOutside {s.v} y → Commute x y := by
  intro L _ _ _ n s x y hx hy
  refine Subtype.ext (Units.ext ?_)
  change (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) =
    (y.1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L))
  ext i j
  rw [← sub_eq_zero]
  refine GlobalTheory.AdelicComp.eq_zero_of_compAt_eq_zero L _ fun w => ?_
  have h : ((x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L w) =
      ((y.1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L w) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases hw : w = s.v
    · subst hw
      rw [map_compAt_eq_one s x hx, one_mul, mul_one]
    · rw [hy w (by simpa using hw), one_mul, mul_one]
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun h i) j
end GlobalTheory.SplitLocComm
