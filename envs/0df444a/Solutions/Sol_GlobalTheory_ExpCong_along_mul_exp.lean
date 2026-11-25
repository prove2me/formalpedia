-- Prove2me | solution 1 for GlobalTheory.ExpCong.along_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:12:58.449264+00:00
-- url     : https://prove2.me/submissions/fa92bf9f-ab40-4ac0-bf0c-60a8711300be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Theorems.Thm_GlobalTheory_ExpCong_along_nil
import Theorems.Thm_GlobalTheory_ExpCong_along_cons
import Theorems.Thm_GlobalTheory_ExpCong_along_add
import Theorems.Thm_GlobalTheory_ExpCong_along_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.ExpCong
variable {A k ι : Type} [CommRing A] [CommRing k] (D : ι → A → A) (c : A →+* k)
namespace GlobalTheory.ExpCong
theorem _root_.solution (hadd : ∀ a f g, D a (f + g) = D a f + D a g)
    (hmul : ∀ a f g, D a (f * g) = f * D a g + g * D a f) (S : Set k) (J : AddSubgroup k)
    (hSJ : ∀ s ∈ S, ∀ j ∈ J, s * j ∈ J) (hJS : ∀ j ∈ J, j ∈ S) (E φ : A) (hE : ∀ a, D a E = E * D a φ)
    (hE1 : c E = 1) (w : List ι) (f : A)
    (hf : ∀ v, v.Sublist w → c (along D v f) ∈ S) (hφ : ∀ v, v.Sublist w → c (along D v φ) ∈ J) :
    c (along D w (f * E)) - c (along D w f) ∈ J := by
  induction w generalizing f with
  | nil =>
    rw [along_nil, along_nil, map_mul, hE1, mul_one, sub_self]
    exact J.zero_mem
  | cons a w ih =>
    have hφ' : ∀ v, v.Sublist w → c (along D v φ) ∈ J := fun v hv => hφ v (hv.cons a)
    have h1 : ∀ v, v.Sublist w → c (along D v (f * D a φ)) ∈ J := fun v hv =>
      along_mul_mem D c hadd hmul S J hSJ v f (D a φ)
        (fun v' hv' => hf v' ((hv'.trans hv).cons a))
        (fun v' hv' => hφ (a :: v') ((hv'.trans hv).cons_cons a))
    have h2 := ih (f * D a φ) (fun v hv => hJS _ (h1 v hv)) hφ'
    have h3 := ih (D a f) (fun v hv => hf (a :: v) (hv.cons_cons a)) hφ'
    have h4 := J.add_mem (J.add_mem h2 (h1 w (List.Sublist.refl _))) h3
    rw [along_cons, along_cons, hmul, hE, along_add D hadd, map_add,
      show f * (E * D a φ) = f * D a φ * E by ring, mul_comm E]
    convert h4 using 1
    ring
end GlobalTheory.ExpCong
