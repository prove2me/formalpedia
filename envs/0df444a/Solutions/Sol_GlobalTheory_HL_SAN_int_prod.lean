-- Prove2me | solution 1 for GlobalTheory.HL.SAN.int_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:49:45.693284+00:00
-- url     : https://prove2.me/submissions/f1dbedba-22b8-4ae4-96da-9002ba36ba4a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
namespace GlobalTheory.HL.SAN
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem hf_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (hI : ∀ i j, H i j ∈ L.O) (x y : Fin n → E) (hx : ∀ j, x j ∈ L.O) (hy : ∀ j, y j ∈ L.O) :
    _root_.GlobalTheory.HL.hf L H x y ∈ L.O := by
  unfold _root_.GlobalTheory.HL.hf
  exact sum_mem fun i _ => sum_mem fun j _ =>
    mul_mem (mul_mem (hx i) (hI i j)) (_root_.GlobalTheory.UnramOrder.cj_mem L (hy j))
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem eich_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (hI : ∀ i j, H i j ∈ L.O) {x u : Fin n → E} {s : E} (hx : ∀ j, x j ∈ L.O)
    (hu : ∀ j, u j ∈ L.O) (hs : s ∈ L.O) {v : Fin n → E} (hv : ∀ j, v j ∈ L.O) (j : Fin n) :
    _root_.GlobalTheory.HL.eich L H x u s v j ∈ L.O := by
  unfold _root_.GlobalTheory.HL.eich
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact sub_mem (add_mem (hv j) (mul_mem (hf_mem_O L hI v u hv hu) (hx j)))
    (mul_mem (hf_mem_O L hI v x hv hx) (add_mem (hu j) (mul_mem hs (hx j))))
end GlobalTheory.HL.SAN
end
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SAN
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.SAN
namespace _root_.GlobalTheory.HL.SAN
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) : ∀ (m : ℕ) (X u : Fin m → Fin N → E) (s : Fin m → E)
    (e : Fin m → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i j, X i j ∈ L.O) → (∀ i j, u i j ∈ L.O) →
    (∀ i, s i ∈ L.O) → (∀ i v, e i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v) →
    ∀ x : Fin N → E, (∀ j, x j ∈ L.O) → ∀ j, (List.ofFn e).prod x j ∈ L.O := by
  intro m
  induction m with
  | zero =>
    intro X u s e _ _ _ _ x hx j
    simpa using hx j
  | succ m ih =>
    intro X u s e hX hu hs he x hx j
    rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply, he 0]
    exact eich_mem_O L hI (hX 0) (hu 0) (hs 0)
      (fun j' => ih (fun i => X i.succ) (fun i => u i.succ) (fun i => s i.succ) (fun i => e i.succ)
        (fun i => hX i.succ) (fun i => hu i.succ) (fun i => hs i.succ) (fun i => he i.succ) x hx j') j
end _root_.GlobalTheory.HL.SAN
end GlobalTheory.HL.SAN
