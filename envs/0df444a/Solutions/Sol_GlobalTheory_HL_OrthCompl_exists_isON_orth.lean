-- Prove2me | solution 1 for GlobalTheory.HL.OrthCompl.exists_isON_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:46:11.317801+00:00
-- url     : https://prove2.me/submissions/c3bc4ddf-8842-4017-abb4-ea4f101015c8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
import Theorems.Thm_GlobalTheory_HL_OrthCompl_hf_eq_zero_symm
import Theorems.Thm_GlobalTheory_HL_OrthCompl_isON_cons
import Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_triple
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OrthCompl
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.OrthCompl
theorem _root_.solution (h : IsHerm L Hm) (y : Fin n → E) (k : ℕ) :
    ∀ (M : Submodule L.O (Fin n → E)) (e : Fin (k + 2) → Fin n → E), (∀ i, e i ∈ M) →
      IsON L Hm e → ∃ u : Fin k → Fin n → E, (∀ i, u i ∈ M ⊓ orthTo L Hm y) ∧ IsON L Hm u := by
  induction k with
  | zero => exact fun M e _ _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro M e hM he
    let f : Fin k → Fin n → E := fun i => e i.succ.succ.succ
    have hf' : IsON L Hm f := fun i j => by simpa [f] using he i.succ.succ.succ j.succ.succ.succ
    have hne : ∀ i j, i ≠ j → hf L Hm (e i) (e j) = 0 := fun i j hij => by
      rw [he, if_neg hij]
    have heq : ∀ i, hf L Hm (e i) (e i) = 1 := fun i => by rw [he, if_pos rfl]
    have hmem : ∀ i : Fin (k + 1 + 2), (∀ j : Fin k, i ≠ j.succ.succ.succ) →
        e i ∈ M ⊓ ⨅ j, orthTo L Hm (f j) := fun i hi =>
      ⟨hM i, (Submodule.mem_iInf _).2 fun j => hne _ _ (hi j)⟩
    obtain ⟨u, hu, t, ht, s, hs, uu, tt, ss, tu, su, st, uy⟩ := exists_triple L h
      (M ⊓ ⨅ j, orthTo L Hm (f j)) (e0 := e 0) (e1 := e (Fin.succ 0))
      (e2 := e (Fin.succ (Fin.succ 0)))
      (hmem _ fun j => (Fin.succ_ne_zero _).symm)
      (hmem _ fun j hj => (Fin.succ_ne_zero _).symm (Fin.succ_injective _ hj))
      (hmem _ fun j hj => (Fin.succ_ne_zero _).symm
        (Fin.succ_injective _ (Fin.succ_injective _ hj)))
      (heq _) (heq _) (heq _) (hne _ _ (Fin.succ_ne_zero _).symm)
      (hne _ _ (Fin.succ_ne_zero _).symm)
      (hne _ _ fun hj => (Fin.succ_ne_zero _).symm (Fin.succ_injective _ hj)) y
    have hfo : ∀ {v}, v ∈ M ⊓ ⨅ j, orthTo L Hm (f j) → ∀ j, hf L Hm (f j) v = 0 :=
      fun hv j => hf_eq_zero_symm L h ((Submodule.mem_iInf _).1 hv.2 j)
    obtain ⟨w, hw, hw'⟩ := ih (M ⊓ orthTo L Hm u)
      (Fin.cons t (Fin.cons s f : Fin (k + 1) → Fin n → E))
      (Fin.cases ⟨ht.1, tu⟩ (Fin.cases ⟨hs.1, su⟩ fun j => ⟨hM _, hfo hu j⟩))
      (isON_cons L h tt (Fin.cases st (hfo ht)) (isON_cons L h ss (hfo hs) hf'))
    exact ⟨Fin.cons u w, Fin.cases ⟨hu.1, uy⟩ fun j => ⟨(hw j).1.1, (hw j).2⟩,
      isON_cons L h uu (fun j => (hw j).1.2) hw'⟩
end GlobalTheory.HL.OrthCompl
