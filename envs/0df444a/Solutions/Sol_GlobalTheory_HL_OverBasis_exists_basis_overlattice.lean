-- Prove2me | solution 1 for GlobalTheory.HL.OverBasis.exists_basis_overlattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:45:49.392815+00:00
-- url     : https://prove2.me/submissions/2b105760-78ec-423d-8347-ae7f2242ef07

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LinearIndependentOfGram
import Theorems.Thm_GlobalTheory_HL_OverBasis_hf_comb
import Theorems.Thm_GlobalTheory_HL_OverBasis_linearIndependent_of_gram
import Theorems.Thm_GlobalTheory_HL_OverBasis_sum_smul_rmul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_SelfDual_exists_eq_span_range
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OverBasis
open Matrix GlobalTheory.HL.SelfDual
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.OverBasis
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (y : Fin m → Fin n → E), IsUnit (gramT L Hm y).det → ∀ Mh : Submodule L.O (Fin n → E), Submodule.span L.O (Set.range y) ≤ Mh → (∀ v ∈ Mh, v ∈ Submodule.span E (Set.range y)) → (∀ v ∈ Mh, ∀ w ∈ Mh, hf L Hm v w ∈ L.O) → LinearIndependent E y ∧ ∃ A : Matrix (Fin m) (Fin m) E, IsIntM L A ∧ IsUnit A.det ∧ Mh = Submodule.span L.O (Set.range (rmul y A⁻¹)) ∧ LinearIndependent E (rmul y A⁻¹) ∧ rmul (rmul y A⁻¹) A = y := by
  intro F _ _ _ _ _ E _ _ _ L n Hm _ m y hG Mh hy hsp hint
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hP : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  have hli := linearIndependent_of_gram L Hm y hG
  refine ⟨hli, ?_⟩
  have hyM : ∀ a, y a ∈ Mh := fun a => hy (Submodule.subset_span ⟨a, rfl⟩)
  let f : (Fin m → L.O) →ₗ[L.O] (Fin n → E) :=
    { toFun := fun w => ∑ i, ((gramT L Hm y)⁻¹ *ᵥ fun a => (w a : E)) i • y i
      map_add' := fun v w => by
        have : (fun a => ((v + w) a : E)) = (fun a => (v a : E)) + fun a => (w a : E) := rfl
        rw [this, Matrix.mulVec_add]
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        have : (fun a => ((c • v) a : E)) = (c : E) • fun a => (v a : E) := rfl
        rw [this, Matrix.mulVec_smul, RingHom.id_apply, Subring.smul_def, Finset.smul_sum]
        simp only [Pi.smul_apply, smul_assoc] }
  have hle : Mh ≤ LinearMap.range f := by
    intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 (hsp v hv)
    refine ⟨fun a => ⟨_, hint _ hv _ (hyM a)⟩, ?_⟩
    show ∑ i, ((gramT L Hm y)⁻¹ *ᵥ fun a => hf L Hm (∑ b, c b • y b) (y a)) i • y i = _
    rw [hf_comb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]
  obtain ⟨b, hb⟩ := exists_eq_span_range m (Mh.comap f)
  let B : Matrix (Fin m) (Fin m) E :=
    Matrix.of fun i j => ((gramT L Hm y)⁻¹ *ᵥ fun a => (b j a : E)) i
  have hM : Mh = Submodule.span L.O (Set.range (rmul y B)) := by
    rw [← Submodule.map_comap_eq_of_le hle, hb, Submodule.map_span, ← Set.range_comp]
    rfl
  have hA : ∀ j, ∃ c : Fin m → L.O, ∑ i, c i • rmul y B i = y j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun L.O).1 (hM ▸ hyM j)
  choose c hc using hA
  let A : Matrix (Fin m) (Fin m) E := Matrix.of fun i j => (c j i : E)
  have hA : rmul (rmul y B) A = y := funext hc
  have hBA : B * A = 1 := by
    ext i j
    have h1 : ∑ i, (B *ᵥ fun k => A k j) i • y i = y j := by
      rw [← sum_smul_rmul]; exact hc j
    have h2 : ∑ i, ((B *ᵥ fun k => A k j) - (Pi.single j 1 : Fin m → E)) i • y i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1]
      simp [Pi.single_apply]
    have h3 := sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h2 i)
    rw [Matrix.one_apply, ← Pi.single_apply, ← h3]
    rfl
  have hinv : A⁻¹ = B := Matrix.inv_eq_left_inv hBA
  refine ⟨A, fun i j => (c j i).2, Matrix.isUnit_det_of_left_inverse hBA, ?_⟩
  rw [hinv]
  refine ⟨hM, ?_, hA⟩
  rw [Fintype.linearIndependent_iff]
  intro d hd
  rw [sum_smul_rmul] at hd
  have h1 : B *ᵥ d = 0 := funext (Fintype.linearIndependent_iff.1 hli _ hd)
  have h2 : A *ᵥ (B *ᵥ d) = d := by
    rw [Matrix.mulVec_mulVec, mul_eq_one_comm.1 hBA, Matrix.one_mulVec]
  rw [h1, Matrix.mulVec_zero] at h2
  exact fun i => congrFun h2.symm i
end GlobalTheory.HL.OverBasis
