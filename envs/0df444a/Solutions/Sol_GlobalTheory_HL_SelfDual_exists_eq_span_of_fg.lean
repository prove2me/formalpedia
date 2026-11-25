-- Prove2me | solution 1 for GlobalTheory.HL.SelfDual.exists_eq_span_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:57.913626+00:00
-- url     : https://prove2.me/submissions/a5e6138d-a0e7-4c71-a0cd-8c96ae0896ca

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Theorems.Thm_GlobalTheory_HL_SelfDual_exists_eq_span_range
import Theorems.Thm_GlobalTheory_HL_SelfDual_exists_mul_mem_finset
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SelfDual
open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.SelfDual
theorem _root_.solution (L : LocE F E) [IsPrincipalIdealRing L.O] {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (h : Λ.FG) :
    ∃ b : Fin n → Fin n → E, Λ = Submodule.span L.O (Set.range b) := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨c, hc, hs⟩ := exists_mul_mem_finset L
    (s.biUnion fun x => Finset.univ.image fun i => x i)
  have hc' : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have h1 : algebraMap F E (c : F)⁻¹ * algebraMap F E c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc', map_one]
  let f : (Fin n → L.O) →ₗ[L.O] (Fin n → E) :=
    { toFun := fun v i => algebraMap F E (c : F)⁻¹ * v i
      map_add' := fun v w => by ext i; simp [mul_add]
      map_smul' := fun a v => by
        ext i
        show _ * ((a : E) * v i) = (a : E) * (_ * _)
        ring }
  have hle : Submodule.span L.O (s : Set (Fin n → E)) ≤ LinearMap.range f := by
    rw [Submodule.span_le]
    intro x hx
    refine ⟨fun i => ⟨algebraMap F E c * x i, hs _ ?_⟩, ?_⟩
    · exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    · ext i
      show algebraMap F E (c : F)⁻¹ * (algebraMap F E c * x i) = _
      rw [← mul_assoc, h1, one_mul]
  obtain ⟨b, hb⟩ := exists_eq_span_range n
    ((Submodule.span L.O (s : Set (Fin n → E))).comap f)
  refine ⟨fun i => f (b i), ?_⟩
  rw [← Submodule.map_comap_eq_of_le hle, hb, Submodule.map_span, ← Set.range_comp]
  rfl
end GlobalTheory.HL.SelfDual
