-- Prove2me | solution 1 for GlobalTheory.HL.PrimVol.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:18.794776+00:00
-- url     : https://prove2.me/submissions/a19811ec-aa87-44ba-85bd-d12aa8978087

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesHermitianGramCosetContent
import Theorems.Thm_GlobalTheory_HL_PrimVol_mem_hermLat
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_GramCount_Prim_map
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimVol
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
namespace GlobalTheory.HL.PrimVol
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    {m : ℕ} (A : AddSubgroup (Matrix (Fin m) (Fin m) E)) (hA : A.relIndex (hermLat L m) ≠ 0) :
    ∃ j, 1 ≤ j ∧ (hermLat L m).map
      (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j))) ≤ A := by
  obtain ⟨-, -, -, -, h5, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  set d := A.relIndex (hermLat L m) with hd
  have hd0 : (d : 𝒪[F]) ≠ 0 := Nat.cast_ne_zero.2 hA
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  refine ⟨k + 1, by omega, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  obtain ⟨h1, h2⟩ := (mem_hermLat L X).1 hX
  let r : 𝒪[F] := ϖ * (u⁻¹ : (𝒪[F])ˣ)
  have hr : ϖ ^ (k + 1) = d * r := by
    rw [hk]
    simp only [r]
    linear_combination (-(ϖ ^ (k + 1))) * u.mul_inv
  have hr' := congrArg (fun x : 𝒪[F] => algebraMap F E (x : F)) hr
  simp only [Subring.coe_mul, map_mul, SubmonoidClass.coe_pow, Subring.coe_natCast, map_natCast] at hr'
  have hY : algebraMap F E (r : F) • X ∈ hermLat L m := by
    refine (mem_hermLat L _).2 ⟨?_, fun a b => L.O.mul_mem ((h5 _).2 r.2) (h2 a b)⟩
    ext i j
    have h1 := congrFun (congrFun h1 i) j
    simp only [cT] at h1
    simp [cT, h1]
  have := AddSubgroup.nsmul_relIndex_mem A hY
  rw [← hd, ← Nat.cast_smul_eq_nsmul E, smul_smul, ← hr'] at this
  exact this
end GlobalTheory.HL.PrimVol
