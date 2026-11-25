-- Prove2me | solution 1 for GlobalTheory.SubmoduleCount.card_submodule_and_hom_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:32:20.965687+00:00
-- url     : https://prove2.me/submissions/f5680620-e811-42a2-aba9-453384afdb4c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.SubmoduleCount
section Abstract
variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D]
end Abstract
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D] in
private theorem exists_finite_generators_of_isPrincipalIdealRing [IsPrincipalIdealRing R] :
    ∀ (g : ℕ) (M : Type) [AddCommGroup M] [Module R M] (x : Fin g → M),
      Submodule.span R (Set.range x) = ⊤ →
        ∀ N : Submodule R M, ∃ v : Fin g → M, N = Submodule.span R (Set.range v) := by
  intro g
  induction g with
  | zero =>
    intro M _ _ x hx N
    refine ⟨Fin.elim0, ?_⟩
    have hbot : (⊤ : Submodule R M) = ⊥ := by
      rw [← hx, Set.range_eq_empty, Submodule.span_empty]
    rw [Set.range_eq_empty, Submodule.span_empty, eq_bot_iff, ← hbot]
    exact le_top
  | succ g ih =>
    intro M _ _ x hx N
    set P := Submodule.span R (Set.range (fun i : Fin g => x i.succ)) with hPdef
    let x' : Fin g → P := fun i => ⟨x i.succ, Submodule.subset_span ⟨i, rfl⟩⟩
    have hx' : Submodule.span R (Set.range x') = ⊤ := by
      apply Submodule.map_injective_of_injective (f := P.subtype) Subtype.val_injective
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      rfl
    obtain ⟨w, hw⟩ := ih P x' hx' (N.comap P.subtype)
    set I : Ideal R := (N ⊔ P).comap (LinearMap.toSpanSingleton R M (x 0)) with hIdef
    set a := Submodule.IsPrincipal.generator I
    have ha : a ∈ I := Submodule.IsPrincipal.generator_mem I
    rw [hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_sup] at ha
    obtain ⟨n, hn, p, hp, hnp⟩ := ha
    refine ⟨Fin.cons n (fun i => (w i : M)), le_antisymm ?_ ?_⟩
    · intro m hm
      have hmtop : m ∈ Submodule.span R (Set.range x) := hx ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmtop
      rw [Fin.sum_univ_succ] at hm ⊢
      set q := ∑ i : Fin g, c i.succ • x i.succ with hqdef
      have hq : q ∈ P := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hc0 : c 0 ∈ I := by
        rw [hIdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
        have := sub_mem (Submodule.mem_sup_left hm : _ ∈ N ⊔ P) (Submodule.mem_sup_right hq : _ ∈ N ⊔ P)
        simpa using this
      rw [← Submodule.IsPrincipal.span_singleton_generator I, Submodule.mem_span_singleton] at hc0
      obtain ⟨t, ht⟩ := hc0
      have hdiff : c 0 • x 0 + q - t • n = q + t • p := by
        rw [← ht, smul_assoc, ← hnp, smul_add]; abel
      have hdP : c 0 • x 0 + q - t • n ∈ P := by
        rw [hdiff]; exact add_mem hq (Submodule.smul_mem _ _ hp)
      have hdN : c 0 • x 0 + q - t • n ∈ N := sub_mem hm (Submodule.smul_mem _ _ hn)
      have hmem : (⟨_, hdP⟩ : P) ∈ Submodule.span R (Set.range w) := hw ▸ hdN
      have hle : Submodule.span R (Set.range w) ≤ (Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M))).comap P.subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i.succ, by simp⟩
      have h1 := hle hmem
      rw [Submodule.mem_comap, Submodule.coe_subtype] at h1
      have h2 : t • n ∈ Submodule.span R (Set.range (Fin.cons n (fun i => (w i : M)) : Fin (g + 1) → M)) :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
      simpa using add_mem h1 h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hn
      · have : w i ∈ N.comap P.subtype := hw ▸ Submodule.subset_span ⟨i, rfl⟩
        simpa using this
end GlobalTheory.SubmoduleCount
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.SubmoduleCount
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.SubmoduleCount
namespace _root_.GlobalTheory.SubmoduleCount
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D] (g : ℕ) (x : Fin g → D), Submodule.span L.O (Set.range x) = ⊤ → Nat.card (Submodule L.O D) ≤ Nat.card D ^ g ∧ ∀ (D' : Type) [AddCommGroup D'] [Module L.O D'] [Finite D'], Nat.card (D →ₗ[L.O] D') ≤ Nat.card D' ^ g := by
  intro F _ _ _ _ _ E _ _ _ L D _ _ _ g x hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation F).integer
  haveI : IsPrincipalIdealRing L.O := (_root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  refine ⟨?_, fun D' _ _ _ => ?_⟩
  · have hsurj : Function.Surjective (fun v : Fin g → D => Submodule.span L.O (Set.range v)) := by
      intro N
      obtain ⟨v, hv⟩ := exists_finite_generators_of_isPrincipalIdealRing g D x hx N
      exact ⟨v, hv.symm⟩
    calc Nat.card (Submodule L.O D) ≤ Nat.card (Fin g → D) := Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card D ^ g := by simp [Nat.card_fun]
  · have hinj : Function.Injective (fun f : D →ₗ[L.O] D' => fun i => f (x i)) := by
      intro f f' h
      exact LinearMap.ext_on_range hx (fun i => congrFun h i)
    calc Nat.card (D →ₗ[L.O] D') ≤ Nat.card (Fin g → D') := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card D' ^ g := by simp [Nat.card_fun]
end _root_.GlobalTheory.SubmoduleCount
end GlobalTheory.SubmoduleCount
