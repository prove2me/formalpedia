-- Prove2me | solution 1 for GlobalTheory.HL.HermJacobian.cont_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:18:47.958646+00:00
-- url     : https://prove2.me/submissions/aa694b3f-0ec7-42a4-b361-5ef42ad8805e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobian
import Theorems.Thm_GlobalTheory_HL_HermJacobian_coord_apply
import Theorems.Thm_GlobalTheory_HL_HermJacobian_coord_symm_apply
import Theorems.Thm_GlobalTheory_HL_HermJacobian_det_sandwich
import Theorems.Thm_GlobalTheory_HL_HermJacobian_det_of_comm
import Theorems.Thm_GlobalTheory_HL_HermJacobian_mem_hermLat_iff
import Theorems.Thm_GlobalTheory_HL_HermJacobian_det_cT
import Theorems.Thm_GlobalTheory_HL_HermJacobian_isHerm_congr
import Theorems.Thm_GlobalTheory_HL_HermJacobian_isHerm_coord
import Theorems.Thm_GlobalTheory_HL_HermJacobian_exists_coord
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_ContAut_cont_image
import Theorems.Thm_GlobalTheory_HL_ContModel_cj_mem
import Theorems.Thm_GlobalTheory_T_relative_lattice_volume_of_det_valuation
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_sub_cj_mul_eq_one
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical Kronecker
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.HermJacobian
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.HermJacobian
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) E), IsUnit A.det → (∀ X, X ∈ hermLat L m ↔ IsHerm L X ∧ IsIntM L X) ∧ ∀ B, IsCO (hermLat L m) B → IsCO (hermLat L m) ((fun X => cT L A * X * A) '' B) ∧ cont (hermLat L m) ((fun X => cT L A * X * A) '' B) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * m)) * cont (hermLat L m) B := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ m A hA
  refine ⟨mem_hermLat_iff L m, fun B hB => ?_⟩
  obtain ⟨ω, hω, e, he, h⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hA' : IsUnit (cT L A).det := by rw [det_cT]; exact hA.map L.cj
  let φ : Matrix (Fin m) (Fin m) E ≃+ Matrix (Fin m) (Fin m) E :=
    { toFun := fun X => cT L A * X * A
      invFun := fun X => (cT L A)⁻¹ * X * A⁻¹
      left_inv := fun X => by
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA',
          Matrix.nonsing_inv_mul_cancel_left _ _ hA', Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
      right_inv := fun X => by
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA',
          Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul] }
  set T := coord m ω (L.cj ω) e h with hT
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 hinj)
  have hr' : ∀ a : F, r (algebraMap F E a) = a := fun a => LinearMap.congr_fun hr a
  let g : (Fin m × Fin m → E) →ₗ[E] (Fin m × Fin m → E) :=
    (T.symm : _ →ₗ[E] _) ∘ₗ sandwich (cT L A) A ∘ₗ (T.symm.symm : _ →ₗ[E] _)
  let ι : (Fin m × Fin m → F) →ₗ[F] (Fin m × Fin m → E) := (Algebra.linearMap F E).compLeft _
  let f : (Fin m × Fin m → F) →ₗ[F] (Fin m × Fin m → F) :=
    r.compLeft _ ∘ₗ g.restrictScalars F ∘ₗ ι
  have hfg : ∀ v, g (fun k => algebraMap F E (v k)) = fun k => algebraMap F E (f v k) := by
    intro v
    funext k
    obtain ⟨a, ha⟩ := exists_coord L h _ (isHerm_congr L A _ (isHerm_coord L h v)) k
    have h1 : g (fun k => algebraMap F E (v k)) k = algebraMap F E a := ha.symm
    have h2 : f v k = r (g (fun k => algebraMap F E (v k)) k) := rfl
    rw [h2, h1, hr']
  obtain ⟨n, hn⟩ := (L.cj_fix (A.det * L.cj A.det)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Nontrivial E := hinj.nontrivial
    exact (hA.mul (hA.map L.cj)).ne_zero (by rw [← hn, map_zero])
  have hdet : LinearMap.det f = n ^ m := by
    apply hinj
    rw [det_of_comm f g hfg, LinearMap.det_conj, det_sandwich, det_cT, map_pow, hn, mul_comm]
  obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 n hn0
  rw [hn] at hu
  let f' : (Fin m × Fin m → F) ≃ₗ[F] (Fin m × Fin m → F) :=
    LinearMap.equivOfIsUnitDet (f := f) (by rw [hdet]; exact (pow_ne_zero _ hn0).isUnit)
  have hf' : (f' : _ →ₗ[F] _) = f := LinearMap.coe_equivOfIsUnitDet _
  let W0 : AddSubgroup (Fin m × Fin m → F) := AddSubgroup.pi Set.univ fun _ => (𝒪[F]).toAddSubgroup
  have hW0 : ∀ x, x ∈ W0 ↔ ∀ i, x i ∈ 𝒪[F] := fun x => by simp [W0, AddSubgroup.mem_pi]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basisFun F (Fin m × Fin m)) f'
    (vE L ϖ (A.det * L.cj A.det) * m) (u ^ m) (by
      rw [hf', hdet, zpow_mul, zpow_natCast]
      conv_lhs => rw [hu]
      rw [mul_pow]
      simp) W0 (fun x => by simpa using hW0 x)
  let j : (Fin m × Fin m → F) →+ Matrix (Fin m) (Fin m) E :=
    T.toAddEquiv.toAddMonoidHom.comp ι.toAddMonoidHom
  have hj : ∀ v, j v = T fun k => algebraMap F E (v k) := fun _ => rfl
  have hjinj : Function.Injective j := fun v w hvw =>
    funext fun k => hinj (congrFun (T.injective hvw) k)
  have hcj := GlobalTheory.UnramOrder.cj_mem L hω
  have hlat : hermLat L m = W0.map j := by
    ext X
    rw [mem_hermLat_iff, AddSubgroup.mem_map]
    constructor
    · rintro ⟨hX, hI⟩
      choose v hv using exists_coord L h X hX
      refine ⟨v, (hW0 v).2 fun ⟨a, b⟩ => ?_, ?_⟩
      · rw [← GlobalTheory.UnramOrder.algebraMap_mem_iff L, hv, coord_symm_apply]
        split_ifs
        · exact L.O.sub_mem (hI _ _) (L.O.mul_mem hω (L.O.mul_mem he (L.O.sub_mem (hI _ _) (hI _ _))))
        · exact L.O.mul_mem he (L.O.sub_mem (hI _ _) (hI _ _))
        · exact hI _ _
      · rw [hj, funext hv]
        exact T.apply_symm_apply X
    · rintro ⟨v, hv, rfl⟩
      have hv' : ∀ k, algebraMap F E (v k) ∈ L.O := fun k =>
        (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 ((hW0 v).1 hv k)
      refine ⟨isHerm_coord L h v, fun a b => ?_⟩
      rw [hj, coord_apply]
      split_ifs
      · exact L.O.add_mem (hv' _) (L.O.mul_mem hω (hv' _))
      · exact L.O.add_mem (hv' _) (L.O.mul_mem hcj (hv' _))
      · exact hv' _
  have hmap : (hermLat L m).map φ.toAddMonoidHom
      = (W0.map f'.toAddEquiv.toAddMonoidHom).map j := by
    rw [hlat, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    refine AddMonoidHom.ext fun v => ?_
    have h4 : f' v = f v := LinearMap.congr_fun hf' v
    show cT L A * j v * A = j (f' v)
    rw [h4, hj, hj, ← hfg]
    exact (T.apply_symm_apply _).symm
  have e1 : ((hermLat L m).map φ.toAddMonoidHom).relIndex (hermLat L m)
      = (W0.map f'.toAddEquiv.toAddMonoidHom).relIndex W0 := by
    rw [hmap, hlat, AddSubgroup.relIndex_map_map_of_injective _ _ hjinj]
  have e2 : (hermLat L m).relIndex ((hermLat L m).map φ.toAddMonoidHom)
      = W0.relIndex (W0.map f'.toAddEquiv.toAddMonoidHom) := by
    rw [hmap, hlat, AddSubgroup.relIndex_map_map_of_injective _ _ hjinj]
  obtain ⟨h5, h6⟩ := GlobalTheory.HL.ContAut.cont_image (hermLat L m) φ (e1 ▸ h1) (e2 ▸ h2) B hB
  refine ⟨h5, h6.trans ?_⟩
  rw [← h3, relVol, relVol, e1, e2]
end GlobalTheory.HL.HermJacobian
