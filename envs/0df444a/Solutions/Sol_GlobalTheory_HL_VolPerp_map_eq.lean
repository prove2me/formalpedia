-- Prove2me | solution 1 for GlobalTheory.HL.VolPerp.map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:42:09.497851+00:00
-- url     : https://prove2.me/submissions/d70cb753-658c-4e50-9c51-90241ff7a425

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualHermitianLatticeTraceOrthogonalVolumeRat
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_DualInter_cj_hf
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.VolPerp
open GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.HL.VolPerp
theorem _root_.solution (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {b c : Fin m → Fin n → E} (hb : ∀ i, b i ∈ Λ) (hc : ∀ i, c i ∈ Λ)
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0)
    (φ : (Fin n → E) →ₗ[E] (Fin m → E)) (w : Fin m → Fin m → E)
    (hφ : ∀ v, φ v = ∑ j, hf L Hm v (b j) • w j) :
    Λ.toAddSubgroup.map φ.toAddMonoidHom = (Submodule.span L.O (Set.range w)).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change φ v ∈ Submodule.span L.O (Set.range w)
    rw [hφ]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem (Submodule.span L.O (Set.range w))
      ⟨_, (hΛ.2 _).2 (hb j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
  · intro hx
    have : Submodule.span L.O (Set.range w) ≤ Λ.map (φ.restrictScalars L.O) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine ⟨c j, hc j, ?_⟩
      have : ∀ i, hf L Hm (c j) (b i) = if i = j then 1 else 0 := fun i => by
        rw [← cj_hf h, hbc]; split_ifs <;> simp
      simp [hφ, this]
    exact this hx
end GlobalTheory.HL.VolPerp
