-- Prove2me | solution 1 for GlobalTheory.UnramOrder.card_coker_of_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:21.565881+00:00
-- url     : https://prove2.me/submissions/248de3bf-69d8-4ce1-bb3b-9572dd71687b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBase
import Theorems.Thm_GlobalTheory_UnramOrder_card_coker_eq_pow_addVal_det
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
import Theorems.Thm_GlobalTheory_UnramOrder_exists_eq_add_mul
import Theorems.Thm_GlobalTheory_UnramOrder_exists_int_of_fixed
import Theorems.Thm_GlobalTheory_UnramOrder_exists_sub_cj_mul_eq_one
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
open GlobalTheory GlobalTheory.UnramOrder
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.UnramOrder
namespace _root_.GlobalTheory.UnramOrder
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι L.O) (j : ℕ) (u : (𝒪[F])ˣ), ((A.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ j * ((u : 𝒪[F]) : F)) → Nat.card ((ι → L.O) ⧸ LinearMap.range A.mulVecLin) = _root_.GlobalTheory.HL.resQ ϖ ^ (2 * j) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ ι _ _ A j u hA
  obtain ⟨-, hO, -, -, hmem, -⟩ := _root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  let φ : 𝒪[F] →+* L.O :=
    { toFun := fun r => ⟨algebraMap F E r, (hmem r).mpr r.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  letI : Algebra 𝒪[F] L.O := φ.toAlgebra
  have hφ : ∀ r : 𝒪[F], ((algebraMap 𝒪[F] L.O r : L.O) : E) = algebraMap F E r := fun r => rfl
  let c : L.O →+* L.O :=
    { toFun := fun x => ⟨L.cj x, (hO x.1 x.2).1⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hc : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun x => rfl
  obtain ⟨ω, hω, e, he, hωe⟩ := _root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  let ω' : L.O := ⟨ω, hω⟩
  have hunit : IsUnit (ω' - c ω') :=
    isUnit_iff_exists_inv.mpr ⟨⟨e, he⟩, Subtype.ext (by simpa [ω', hc] using hωe)⟩
  have hdecomp := _root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := 𝒪[F]) c
    (fun x => Subtype.ext (by simp [hc, L.cj_cj]))
    (fun r => Subtype.ext (by simp [hc, hφ]))
    (fun x hx => by
      obtain ⟨r, hr⟩ := _root_.GlobalTheory.UnramOrder.exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
      exact ⟨r, Subtype.ext (by rw [hφ, ← hr])⟩) hunit
  have hinjO : Function.Injective (algebraMap 𝒪[F] L.O) := by
    intro r s h
    have h' := congrArg Subtype.val h
    rw [hφ, hφ] at h'
    exact Subtype.ext (_root_.GlobalTheory.UnramOrder.algebraMap_inj L h')
  have hli : LinearIndependent 𝒪[F] ![(1 : L.O), ω'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have hst' := congrArg c hst
    rw [map_add, map_mul, map_zero] at hst'
    have hfix : ∀ r : 𝒪[F], c (algebraMap 𝒪[F] L.O r) = algebraMap 𝒪[F] L.O r :=
      fun r => Subtype.ext (by simp [hc, hφ])
    rw [hfix, hfix] at hst'
    have ht0 : algebraMap 𝒪[F] L.O t * (ω' - c ω') = 0 := by
      rw [mul_sub]
      linear_combination hst - hst'
    have ht : t = 0 := hinjO (by rw [map_zero]; exact (hunit.mul_left_eq_zero).mp ht0)
    refine ⟨hinjO ?_, ht⟩
    rw [ht, map_zero, zero_mul, add_zero] at hst
    rw [hst, map_zero]
  have hspan : ⊤ ≤ Submodule.span 𝒪[F] (Set.range ![(1 : L.O), ω']) := by
    intro x _
    obtain ⟨a, b, hx⟩ := hdecomp x
    have hx' : x = a • ![(1 : L.O), ω'] 0 + b • ![(1 : L.O), ω'] 1 := by
      simp [hx, Algebra.smul_def]
    rw [hx']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let bO := Module.Basis.mk hli hspan
  haveI : Module.Free 𝒪[F] L.O := Module.Free.of_basis bO
  haveI : Module.Finite 𝒪[F] L.O := Module.Finite.of_basis bO
  have hrank : Module.finrank 𝒪[F] L.O = 2 := by
    rw [Module.finrank_eq_card_basis bO, Fintype.card_fin]
  have hdetA : A.det = algebraMap 𝒪[F] L.O (ϖ ^ j * (u : 𝒪[F])) := by
    apply Subtype.ext
    rw [hA, hφ]
    push_cast
    rfl
  have hdetf : LinearMap.det (A.mulVecLin.restrictScalars 𝒪[F]) =
      (ϖ ^ j * (u : 𝒪[F])) ^ 2 := by
    rw [LinearMap.det_restrictScalars]
    change Algebra.norm 𝒪[F] (LinearMap.det (Matrix.toLin' A)) = _
    rw [LinearMap.det_toLin', hdetA, Algebra.norm_algebraMap, hrank]
  have hne : (ϖ ^ j * (u : 𝒪[F])) ^ 2 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) u.ne_zero)
  have h1 := _root_.GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det (A.mulVecLin.restrictScalars 𝒪[F])
    (by rw [hdetf]; exact hne)
  rw [LinearMap.range_restrictScalars,
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv 𝒪[F] _).toEquiv] at h1
  rw [h1, hdetf, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit u, add_zero]
  have hres : Nat.card (IsLocalRing.ResidueField 𝒪[F]) = _root_.GlobalTheory.HL.resQ ϖ := by
    unfold _root_.GlobalTheory.HL.resQ
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    rfl
  rw [hres]
  congr 1
  simp [mul_comm]
end _root_.GlobalTheory.UnramOrder
end GlobalTheory.UnramOrder
