-- Prove2me | solution 1 for GlobalTheory.MatrixIndex.index_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:06:44.276626+00:00
-- url     : https://prove2.me/submissions/c0417202-179f-4ef7-8382-39458f114da1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanEqMap
import Theorems.Thm_GlobalTheory_MatrixIndex_exists_basis
import Theorems.Thm_GlobalTheory_MatrixIndex_span_eq_map
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_relative_lattice_volume_of_det_valuation
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramVal_vE_valuation
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
open GlobalTheory GlobalTheory.MatrixIndex
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.MatrixIndex
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n m : ℕ} (y : Fin m → Fin n → E), LinearIndependent E y → ∀ A : Matrix (Fin m) (Fin m) E, IsIntM L A → IsUnit A.det → 0 ≤ vE L ϖ (A.det * L.cj A.det) ∧ (Submodule.span L.O (Set.range (rmul y A))).toAddSubgroup.relIndex (Submodule.span L.O (Set.range y)).toAddSubgroup = resQ ϖ ^ (vE L ϖ (A.det * L.cj A.det)).toNat := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n m y hy A hA hu
  obtain ⟨b, hbO, hnorm⟩ := exists_basis L
  have := L.free
  have : Module.Finite F E := Module.Finite.of_basis b
  obtain ⟨-, -, hv3, hv4⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hdO : A.det ∈ L.O := by
    rw [Matrix.det_apply']
    exact L.O.sum_mem fun σ _ => L.O.mul_mem (intCast_mem _ _) (L.O.prod_mem fun i _ => hA _ _)
  have hN0 : Algebra.norm F A.det ≠ 0 := (hu.map (Algebra.norm F)).ne_zero
  have hNO : Algebra.norm F A.det ∈ 𝒪[F] := by
    rw [← GlobalTheory.UnramOrder.algebraMap_mem_iff L, hnorm]
    exact L.O.mul_mem hdO (GlobalTheory.UnramOrder.cj_mem L hdO)
  rw [← hnorm]
  have ha := (hv3 _ hN0).2 hNO
  obtain ⟨u, hu'⟩ := hv4 _ hN0
  refine ⟨ha, ?_⟩
  generalize vE L ϖ (algebraMap F E (Algebra.norm F A.det)) = a at *
  let φ : (Fin m → E) ≃ₗ[F] (Fin m → E) :=
    (Matrix.toLinearEquiv (Pi.basisFun E (Fin m)) A hu).restrictScalars F
  have hφ : ∀ v, φ v = A.mulVec v := fun v => by
    simp [φ, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin']
  have hdet : LinearMap.det (φ : (Fin m → E) →ₗ[F] (Fin m → E)) = Algebra.norm F A.det := by
    have : (φ : (Fin m → E) →ₗ[F] (Fin m → E)) = (Matrix.toLin' A).restrictScalars F := by
      ext1 v; exact LinearMap.ext fun w => hφ _
    rw [this, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  set W0 := (AddSubgroup.pi Set.univ fun _ : Fin m => L.O.toAddSubgroup) with hW0
  have hmem : ∀ x, x ∈ W0 ↔ ∀ i, x i ∈ L.O := fun x => by
    simp [hW0, AddSubgroup.mem_pi]
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basis fun _ : Fin m => b) φ a u (hdet.trans hu') W0
    (fun x => by
      simp only [hmem, hbO, Pi.basis_repr, Sigma.forall])
  have hle : W0.map φ.toAddEquiv.toAddMonoidHom ≤ W0 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hmem]
    intro i
    change φ v i ∈ _
    rw [hφ, Matrix.mulVec, dotProduct]
    exact L.O.sum_mem fun j _ => L.O.mul_mem (hA _ _) ((hmem v).1 hv j)
  have hcomp : (Fintype.linearCombination E (rmul y A)).toAddMonoidHom =
      (Fintype.linearCombination E y).toAddMonoidHom.comp φ.toAddEquiv.toAddMonoidHom := by
    refine AddMonoidHom.ext fun v => ?_
    change Fintype.linearCombination E (rmul y A) v = Fintype.linearCombination E y (φ v)
    rw [hφ]
    simp only [Fintype.linearCombination_apply, rmul, Matrix.mulVec, dotProduct, Finset.smul_sum,
      Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hinj : Function.Injective (Fintype.linearCombination E y).toAddMonoidHom := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact funext (Fintype.linearIndependent_iff.1 hy v hv)
  rw [span_eq_map, span_eq_map, ← hW0, hcomp, ← AddSubgroup.map_map,
    AddSubgroup.relIndex_map_map_of_injective _ _
      hinj]
  rw [relVol, AddSubgroup.relIndex_eq_one.2 hle] at h3
  lift a to ℕ using ha
  rw [zpow_neg, zpow_natCast, Nat.cast_one, one_div, inv_inj] at h3
  rw [Int.toNat_natCast]
  exact_mod_cast h3
end GlobalTheory.MatrixIndex
