-- Prove2me | solution 1 for GlobalTheory.HL.DivisibleGauss.relIndex_divBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:31:29.871864+00:00
-- url     : https://prove2.me/submissions/5ac48a40-3626-4f62-8b03-799e5ad7146b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSum
import Theorems.Thm_GlobalTheory_HL_DivisibleGauss_form_smul_left
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
open scoped Pointwise ENNReal Classical ComplexConjugate
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DivisibleGauss
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HL.DivisibleGauss
theorem _root_.solution (U : Submodule L.O (Fin n → E))
    (hU : ∀ x ∈ U, ∀ y ∈ U, hf L Hm x y ∈ L.O) {ρ : ℕ} (e : Fin ρ → Fin n → E)
    (he : ∀ a, e a ∈ U) (hee : ∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) (x : L.O) :
    (divBy L Hm U e x).relIndex U.toAddSubgroup
      = (Ideal.span {x}).toAddSubgroup.index ^ ρ := by
  let φ : U.toAddSubgroup →+ (Fin ρ → L.O) :=
    AddMonoidHom.mk' (fun u a => ⟨hf L Hm u (e a), hU u u.2 _ (he a)⟩) fun u w =>
      funext fun a => Subtype.ext (form_add_left L Hm _ _ _)
  have hφ : Function.Surjective φ := fun c => by
    refine ⟨⟨∑ b, (c b : E) • e b, U.sum_mem fun b _ => U.smul_mem (c b) (he b)⟩,
      funext fun a => Subtype.ext ?_⟩
    show formLeft L Hm (e a) (∑ b, (c b : E) • e b) = c a
    rw [map_sum]
    show ∑ b, hf L Hm ((c b : E) • e b) (e a) = c a
    simp [form_smul_left, hee]
  have h1 : (divBy L Hm U e x).addSubgroupOf U.toAddSubgroup
      = (AddSubgroup.pi Set.univ fun _ => (Ideal.span {x}).toAddSubgroup).comap φ := by
    ext u
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, true_implies,
      Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨-, h⟩ a
      obtain ⟨c, hc, h⟩ := h a
      exact ⟨⟨c, hc⟩, Subtype.ext h⟩
    · refine fun h => ⟨u.2, fun a => ?_⟩
      obtain ⟨c, h⟩ := h a
      exact ⟨c, c.2, congrArg Subtype.val h⟩
  rw [AddSubgroup.relIndex, h1, AddSubgroup.index_comap_of_surjective _ hφ,
    AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end GlobalTheory.HL.DivisibleGauss
