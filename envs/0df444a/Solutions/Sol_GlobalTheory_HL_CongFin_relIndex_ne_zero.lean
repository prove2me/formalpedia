-- Prove2me | solution 1 for GlobalTheory.HL.CongFin.relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:14:36.189581+00:00
-- url     : https://prove2.me/submissions/f4337cf2-2901-498c-8eab-cbcfbd640031

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CongFin
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {O : Subring E}
namespace GlobalTheory.HL.CongFin
theorem _root_.solution (Λ : Submodule O V) (hΛ : Λ.FG) {c : E} (hc : c ∈ O)
    (hfin : Finite (O ⧸ Ideal.span {(⟨c, hc⟩ : O)})) :
    (congSub Λ c).relIndex (MulAction.stabilizer (V ≃ₗ[E] V) Λ) ≠ 0 := by
  set I : Ideal O := Ideal.span {(⟨c, hc⟩ : O)} with hI
  haveI : Module.Finite O Λ := Module.Finite.iff_fg.2 hΛ
  haveI : Finite (Λ ⧸ (I • ⊤ : Submodule O Λ)) :=
    Submodule.finite_quotient_smul I (Module.Finite.fg_top)
  have hQ : ∀ x y : Λ, (Submodule.Quotient.mk x : Λ ⧸ (I • ⊤ : Submodule O Λ)) = Submodule.Quotient.mk y →
      ∃ w ∈ Λ, (x : V) - y = c • w := by
    intro x y h
    rw [Submodule.Quotient.eq, hI, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨w, -, hw⟩ := h
    exact ⟨w, w.2, (congrArg Subtype.val hw).symm⟩
  set S := MulAction.stabilizer (V ≃ₗ[E] V) Λ
  let f : S → (Λ ⧸ (I • ⊤ : Submodule O Λ)) → (Λ ⧸ (I • ⊤ : Submodule O Λ)) :=
    fun g q => Submodule.Quotient.mk ⟨g.1 (q.out : Λ), ((mem_stab_iff Λ _).1 g.2 _).2 q.out.2⟩
  have hf : ∀ g h : S, f g = f h → g⁻¹ * h ∈ (congSub Λ c).subgroupOf S := by
    intro g h hgh
    rw [Subgroup.mem_subgroupOf]
    refine ⟨(g⁻¹ * h).2, fun v hv => ?_⟩
    let q : Λ ⧸ (I • ⊤ : Submodule O Λ) := Submodule.Quotient.mk ⟨v, hv⟩
    obtain ⟨w, hw, e1⟩ := hQ ⟨v, hv⟩ q.out (Quotient.out_eq q).symm
    obtain ⟨w', hw', e2⟩ := hQ _ _ (congrFun hgh q).symm
    have hi := (mem_stab_iff Λ _).1 (inv_mem g.2)
    have hh := (mem_stab_iff Λ _).1 h.2
    refine ⟨g.1⁻¹ (h.1 w) + g.1⁻¹ w' - w,
      Λ.sub_mem (Λ.add_mem ((hi _).2 ((hh _).2 hw)) ((hi _).2 hw')) hw, ?_⟩
    have e3 : v = (q.out : Λ) + c • w := by rw [← e1]; simp
    have e4 : h.1 (q.out : Λ) = g.1 (q.out : Λ) + c • w' := by rw [← e2]; simp
    have e5 : ∀ x, g.1⁻¹ (g.1 x) = x := fun x => g.1.symm_apply_apply x
    show g.1⁻¹ (h.1 v) - v = _
    rw [e3, map_add, e4]
    simp only [map_add, map_smul, e5, smul_add, smul_sub]
    abel
  have : Finite (S ⧸ (congSub Λ c).subgroupOf S) := by
    refine Finite.of_injective (fun q => f q.out) fun q q' h => ?_
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    exact hf _ _ h
  exact Subgroup.index_ne_zero_of_finite
end GlobalTheory.HL.CongFin
