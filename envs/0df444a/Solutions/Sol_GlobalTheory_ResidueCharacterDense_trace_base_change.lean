-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.trace_base_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:58.503041+00:00
-- url     : https://prove2.me/submissions/ad96b89c-f1b5-4da6-bb4a-da05fdcab7af

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
namespace GlobalTheory.ResidueCharacterDense
theorem _root_.solution {F E K L : Type} [Field F] [Field E] [Algebra F E] [Field K]
    [CommRing L] [Algebra K L] [Module.Free K L] (hE : Module.finrank F E = 2)
    (hL : Module.finrank K L = 2) (f : F →+* K) (g : E →+* L)
    (hc : ∀ a : F, g (algebraMap F E a) = algebraMap K L (f a))
    (hs : Submodule.span K (Set.range g) = ⊤) (x : E) :
    Algebra.trace K L (g x) = f (Algebra.trace F E x) := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq F E hE
  have key : ∀ y : E, g y = ∑ i, f (b.repr y i) • g (b i) := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun i => g (b i)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [key y]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let c := basisOfTopLeSpanOfCardEqFinrank (fun i => g (b i)) hsp (by simp [hL])
  have hcb : ∀ i, c i = g (b i) := fun i => by simp [c]
  have hr : ∀ y i, c.repr (g y) i = f (b.repr y i) := by
    intro y i
    rw [key y]
    simp_rw [← hcb]
    exact congrFun (c.repr_sum_self _) i
  rw [Algebra.trace_eq_matrix_trace c, Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hcb, ← map_mul, hr]
end GlobalTheory.ResidueCharacterDense
