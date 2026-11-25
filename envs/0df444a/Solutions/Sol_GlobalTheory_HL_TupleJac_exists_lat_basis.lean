-- Prove2me | solution 1 for GlobalTheory.HL.TupleJac.exists_lat_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:11.518333+00:00
-- url     : https://prove2.me/submissions/031ff5fe-42e3-4e6c-8d8c-b62b45c060b4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometry
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_SelfDual_orthonormal_basis_and_one_orbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TupleJac
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.TupleJac
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (hH : IsHermND L Hm) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) :
    ∃ B : Module.Basis (Fin n) E (Fin n → E), ∀ x, x ∈ Λ ↔ ∀ i, B.repr x i ∈ L.O := by
  obtain ⟨b, hb, rfl⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).1 Λ hΛ
  have hli : LinearIndependent E b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    let f : (Fin n → E) →ₗ[E] E :=
      { toFun := fun x => hf L Hm x (b j)
        map_add' := fun x y => by simp [hf, add_mul, Finset.sum_add_distrib]
        map_smul' := fun c x => by simp [hf, Finset.mul_sum, mul_assoc] }
    have hfb : ∀ i, f (b i) = if i = j then 1 else 0 := fun i => hb i j
    have := congrArg f hg
    simpa [map_sum, hfb] using this
  have hsp : ⊤ ≤ Submodule.span E (Set.range b) := by
    rw [← hΛ.1.2, Submodule.span_span_of_tower]
  refine ⟨Module.Basis.mk hli hsp, fun x => ?_⟩
  set B := Module.Basis.mk hli hsp with hB
  have hBb : ∀ i, B i = b i := fun i => by simp [hB]
  constructor
  · intro hx i
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    have : ∑ j, c j • b j = ∑ j, (c j : E) • B j := by simp only [hBb]; rfl
    rw [this, B.repr_sum_self]
    exact (c i).2
  · intro hx
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨_, hx i⟩, ?_⟩
    conv_rhs => rw [← B.sum_repr x]
    simp only [hBb]; rfl
end GlobalTheory.HL.TupleJac
