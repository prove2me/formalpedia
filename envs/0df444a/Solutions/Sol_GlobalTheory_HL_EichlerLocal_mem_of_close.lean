-- Prove2me | solution 1 for GlobalTheory.HL.EichlerLocal.mem_of_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:35:20.807043+00:00
-- url     : https://prove2.me/submissions/3c9aa924-bd5c-4df5-837e-62314c71da78

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantData
import Theorems.Thm_P2M_GlobalTheory_HL_EichlerLocal_smul_mem__68d4331394de
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_eich_inv
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_neg_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichlerLocal
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.HL.EichlerLocal
theorem _root_.solution (hH : IsHerm L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    {p : E} (hp : p ∈ L.O) (hpc : L.cj p = p) {x u a b : Fin n → E} {s t : E}
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u)
    (hxΛ : p • x ∈ Λ) (huΛ : u ∈ Λ) (hsO : s ∈ L.O) (ha : a ∈ Λ) (hb : b ∈ Λ) (ht : t ∈ L.O)
    {v : Fin n → E} (hv : eich L Hm x u s v ∈ Λ) :
    eich L Hm (x + p ^ 4 • a) (u + p ^ 4 • b) (s + p ^ 4 * t) v ∈ Λ := by
  have hint : ∀ {y z}, y ∈ Λ → z ∈ Λ → hf L Hm y z ∈ L.O := fun hy hz => (hΛ.2 _).2 hz _ hy
  have hV : p ^ 2 • v ∈ Λ := by
    rw [← eich_inv L hH x u s hx hu hs v]
    generalize eich L Hm x u s v = w at hv
    have e : p ^ 2 • eich L Hm x (-u) (L.cj s) w = p ^ 2 • w - (p * hf L Hm w u) • (p • x)
        + (p * hf L Hm w (p • x)) • u - (hf L Hm w (p • x) * L.cj s) • (p • x) := by
      simp only [eich, hf_neg_r, hf_smul_r, hpc]
      module
    rw [e]
    exact Λ.sub_mem (Λ.add_mem (Λ.sub_mem (smul_mem' L (L.O.pow_mem hp 2) hv)
      (smul_mem' L (L.O.mul_mem hp (hint hv huΛ)) hxΛ))
      (smul_mem' L (L.O.mul_mem hp (hint hv hxΛ)) huΛ))
      (smul_mem' L (L.O.mul_mem (hint hv hxΛ) (GlobalTheory.UnramOrder.cj_mem L hsO)) hxΛ)
  have hu1 : u + p ^ 4 • b ∈ Λ := Λ.add_mem huΛ (smul_mem' L (L.O.pow_mem hp 4) hb)
  have hx1 : p • x + p ^ 5 • a ∈ Λ := Λ.add_mem hxΛ (smul_mem' L (L.O.pow_mem hp 5) ha)
  have hs1 : s + p ^ 4 * t ∈ L.O := L.O.add_mem hsO (L.O.mul_mem (L.O.pow_mem hp 4) ht)
  have e : eich L Hm (x + p ^ 4 • a) (u + p ^ 4 • b) (s + p ^ 4 * t) v = eich L Hm x u s v
      + (p * hf L Hm (p ^ 2 • v) b) • (p • x) + (p ^ 2 * hf L Hm (p ^ 2 • v) (u + p ^ 4 • b)) • a
      - (p * hf L Hm (p ^ 2 • v) (p • x)) • b - (p ^ 2 * hf L Hm (p ^ 2 • v) a) • (u + p ^ 4 • b)
      - (p * hf L Hm (p ^ 2 • v) a * (s + p ^ 4 * t)) • (p • x + p ^ 5 • a)
      - (hf L Hm (p ^ 2 • v) (p • x) * t) • (p • x + p ^ 5 • a)
      - (p * hf L Hm (p ^ 2 • v) (p • x) * s) • a := by
    simp only [eich, hf_add_r, hf_smul_r, hf_smul_l, map_pow, hpc]
    module
  rw [e]
  have hp2 := L.O.pow_mem hp 2
  exact Λ.sub_mem (Λ.sub_mem (Λ.sub_mem (Λ.sub_mem (Λ.sub_mem (Λ.add_mem (Λ.add_mem hv
    (smul_mem' L (L.O.mul_mem hp (hint hV hb)) hxΛ))
    (smul_mem' L (L.O.mul_mem hp2 (hint hV hu1)) ha))
    (smul_mem' L (L.O.mul_mem hp (hint hV hxΛ)) hb))
    (smul_mem' L (L.O.mul_mem hp2 (hint hV ha)) hu1))
    (smul_mem' L (L.O.mul_mem (L.O.mul_mem hp (hint hV ha)) hs1) hx1))
    (smul_mem' L (L.O.mul_mem (hint hV hxΛ) ht) hx1))
    (smul_mem' L (L.O.mul_mem (L.O.mul_mem hp (hint hV hxΛ)) hsO) ha)
end GlobalTheory.HL.EichlerLocal
