-- Prove2me | solution 1 for GlobalTheory.HL.DualInter.exists_denom_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:49:59.758872+00:00
-- url     : https://prove2.me/submissions/60c91fea-b935-48e0-8b36-c536242e3a9c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Theorems.Thm_GlobalTheory_HL_DualInter_smul_l
import Theorems.Thm_GlobalTheory_HL_DualInter_exists_denom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
variable {L Hm}
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.HL.DualInter
theorem _root_.solution {Λ : Submodule L.O (Fin n → E)} (hΛ : Λ.FG) (y : Fin n → E) :
    ∃ d ∈ L.O, IsUnit d ∧ ∀ x ∈ Λ, d * hf L Hm x y ∈ L.O := by
  induction Λ, hΛ using Submodule.fg_induction with
  | singleton v =>
    obtain ⟨d, h1, h2, h3⟩ := exists_denom L (hf L Hm v y)
    refine ⟨d, h1, h2, fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have : hf L Hm (a • v) y = a * hf L Hm v y := smul_l L Hm a v y
    rw [this, mul_left_comm]
    exact L.O.mul_mem a.2 h3
  | sup A B _ _ hA hB =>
    obtain ⟨d, h1, h2, h3⟩ := hA
    obtain ⟨e, k1, k2, k3⟩ := hB
    refine ⟨d * e, L.O.mul_mem h1 k1, h2.mul k2, fun x hx => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := (hfL L Hm y).map_add a b
    rw [this, show d * e * (hf L Hm a y + hf L Hm b y)
      = e * (d * hf L Hm a y) + d * (e * hf L Hm b y) by ring]
    exact L.O.add_mem (L.O.mul_mem k1 (h3 a ha)) (L.O.mul_mem h1 (k3 b hb))
end GlobalTheory.HL.DualInter
