-- Prove2me | solution 1 for GlobalTheory.FrameDual.exists_unip_change_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:42:58.013014+00:00
-- url     : https://prove2.me/submissions/6eb996d3-9a54-4ae9-9932-3f4695295fc9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFrameUnipotentExchangingDualIsotropic
import Theorems.Thm_GlobalTheory_FrameDual_hf_sum_l
import Theorems.Thm_GlobalTheory_FrameDual_hf_sum_r
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FramePsi_hf_span_right
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_l
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_r
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameDual
open GlobalTheory.HL.Eichler
namespace GlobalTheory.FrameDual
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (t : E) (gs gs2 : Fin r → S.V), (∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0) → (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) → (∀ a j, hf L S.Hm (g a) (gs2 j) = if a = j.castSucc then 1 else 0) → (∀ i j, hf L S.Hm (gs i) (gs j) = 0) → (∀ i j, hf L S.Hm (gs2 i) (gs2 j) = 0) → ∃ m ∈ S.Nof g, (∀ a, m (g a) = g a) ∧ (∀ j, m (gs j) = gs2 j) ∧ ∀ A : Submodule L.O S.V, (∀ x ∈ S.spanTo g r, x ∈ A) → (∀ x ∈ A, x ∈ perp L S.Hm (S.spanTo g r)) → m • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O) = A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs2))).restrictScalars L.O := by
  intro F _ _ _ _ _ E _ _ _ L r k S g t gs gs2 hg hd hd2 hi hi2
  have hcj := hf_cj L S.herm.1
  obtain ⟨G, hG⟩ : ∃ G : Fin r → S.V, ∀ j, G j = g j.castSucc := ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin r → S.V, ∀ j, w j = gs2 j - gs j := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin r → S.V, ∀ j, u j = w j + ∑ i, hf L S.Hm (gs j) (w i) • G i :=
    ⟨_, fun _ => rfl⟩
  have hGa : ∀ i a, hf L S.Hm (G i) (g a) = 0 := fun i a => by
    rw [hG, hg, if_neg]; rintro ⟨h, -⟩; exact Fin.castSucc_ne_last i h
  have haG : ∀ a i, hf L S.Hm (g a) (G i) = 0 := fun a i => by
    rw [hG, hg, if_neg]; rintro ⟨-, h⟩; exact Fin.castSucc_ne_last i h
  have hGG : ∀ i j, hf L S.Hm (G i) (G j) = 0 := fun i j => by rw [hG j]; exact hGa i _
  have hgw : ∀ a i, hf L S.Hm (g a) (w i) = 0 := fun a i => by rw [hw, hf_sub_r, hd, hd2, sub_self]
  have hwg : ∀ i a, hf L S.Hm (w i) (g a) = 0 := fun i a => by rw [← hcj, hgw, map_zero]
  have hGw : ∀ i j, hf L S.Hm (G i) (w j) = 0 := fun i j => by rw [hG i]; exact hgw _ _
  have hwG : ∀ i j, hf L S.Hm (w i) (G j) = 0 := fun i j => by rw [hG j]; exact hwg _ _
  have hGu : ∀ i j, hf L S.Hm (G i) (u j) = 0 := fun i j => by
    simp only [hu, hf_add_r, hf_sum_r, hf_smul_r, hGw, hGG, mul_zero, Finset.sum_const_zero, add_zero]
  have huG : ∀ j i, hf L S.Hm (u j) (G i) = 0 := fun j i => by
    simp only [hu, hf_add_l, hf_sum_l, hf_smul_l, hwG, hGG, mul_zero, Finset.sum_const_zero, add_zero]
  have huw : ∀ j i, hf L S.Hm (u j) (w i) = hf L S.Hm (w j) (w i) := fun j i => by
    simp only [hu, hf_add_l, hf_sum_l, hf_smul_l, hGw, mul_zero, Finset.sum_const_zero, add_zero]
  have huu : ∀ j l, hf L S.Hm (u j) (u l) = hf L S.Hm (w j) (w l) := fun j l => by
    conv_lhs => rw [hu l]
    simp only [hf_add_r, hf_sum_r, hf_smul_r, huG, huw, mul_zero, Finset.sum_const_zero, add_zero]
  have hgsG : ∀ j l, hf L S.Hm (gs j) (G l) = if l = j then 1 else 0 := fun j l => by
    rw [← hcj, hG, hd]
    by_cases h : l = j
    · subst h; simp
    · rw [if_neg (fun e => h (Fin.castSucc_injective _ e)), if_neg h, map_zero]
  have K : ∀ j i, hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (gs i) + hf L S.Hm (w j) (w i) = 0 := by
    intro j i
    have e : ∀ j, gs2 j = gs j + w j := fun j => by rw [hw]; abel
    have h2 := hi2 j i
    rw [e, e, hf_add_l, hf_add_r, hf_add_r, hi] at h2
    linear_combination h2

  obtain ⟨ff, hff⟩ : ∃ ff : S.V → S.V, ∀ v, ff v = v + ∑ j, hf L S.Hm v (G j) • u j -
      ∑ i, hf L S.Hm v (w i) • G i := ⟨_, fun _ => rfl⟩
  obtain ⟨fi, hfi⟩ : ∃ fi : S.V → S.V, ∀ v, fi v = v - ∑ j, hf L S.Hm v (G j) • u j +
      ∑ i, (hf L S.Hm v (w i) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w i)) • G i :=
    ⟨_, fun _ => rfl⟩
  have hff_l : ∀ v y, hf L S.Hm (ff v) y = hf L S.Hm v y + ∑ j, hf L S.Hm v (G j) * hf L S.Hm (u j) y -
      ∑ i, hf L S.Hm v (w i) * hf L S.Hm (G i) y := fun v y => by
    rw [hff]; simp only [hf_add_l, hf_sub_l, hf_sum_l, hf_smul_l]
  have hff_r : ∀ y v, hf L S.Hm y (ff v) = hf L S.Hm y v + ∑ j, hf L S.Hm (G j) v * hf L S.Hm y (u j) -
      ∑ i, hf L S.Hm (w i) v * hf L S.Hm y (G i) := fun y v => by
    rw [hff]; simp only [hf_add_r, hf_sub_r, hf_sum_r, hf_smul_r, hcj]
  have hfi_l : ∀ v y, hf L S.Hm (fi v) y = hf L S.Hm v y - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (u j) y +
      ∑ i, (hf L S.Hm v (w i) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w i)) * hf L S.Hm (G i) y :=
    fun v y => by
    rw [hfi]; simp only [hf_add_l, hf_sub_l, hf_sum_l, hf_smul_l]
  have h1 : ∀ v, ff (fi v) = v := fun v => by
    have eG : ∀ l, hf L S.Hm (fi v) (G l) = hf L S.Hm v (G l) := fun l => by
      simp only [hfi_l, huG, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
    have ew : ∀ l, hf L S.Hm (fi v) (w l) =
        hf L S.Hm v (w l) - ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w l) := fun l => by
      simp only [hfi_l, huw, hGw, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hff]; simp only [eG, ew]; rw [hfi]; abel
  have h2 : ∀ v, fi (ff v) = v := fun v => by
    have eG : ∀ l, hf L S.Hm (ff v) (G l) = hf L S.Hm v (G l) := fun l => by
      simp only [hff_l, huG, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
    have ew : ∀ l, hf L S.Hm (ff v) (w l) =
        hf L S.Hm v (w l) + ∑ j, hf L S.Hm v (G j) * hf L S.Hm (w j) (w l) := fun l => by
      simp only [hff_l, huw, hGw, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [hfi]; simp only [eG, ew, add_sub_cancel_right]; rw [hff]; abel
  obtain ⟨m, hm⟩ : ∃ m : S.GLV, ∀ v, m v = ff v := by
    refine ⟨{ toFun := ff, invFun := fi, left_inv := h2, right_inv := h1, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
    · intro x y; simp only [hff, hf_add_l, add_smul, Finset.sum_add_distrib]; abel
    · intro c x; simp only [hff, hf_smul_l, smul_add, smul_sub, Finset.smul_sum, mul_smul, RingHom.id_apply]
  have iso : ∀ v v', hf L S.Hm (ff v) (ff v') = hf L S.Hm v v' := by
    intro v v'
    rw [hff_l]
    simp only [hff_r, huu, huG, hGu, hGG, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]

    have hvu : ∀ j, hf L S.Hm v (u j) = hf L S.Hm v (w j) + ∑ i, hf L S.Hm (w i) (gs j) * hf L S.Hm v (G i) := by
      intro j; rw [hu, hf_add_r, hf_sum_r]; simp only [hf_smul_r, hcj]
    have huv : ∀ j, hf L S.Hm (u j) v' = hf L S.Hm (w j) v' + ∑ i, hf L S.Hm (gs j) (w i) * hf L S.Hm (G i) v' := by
      intro j; rw [hu, hf_add_l, hf_sum_l]; simp only [hf_smul_l]
    simp only [hvu, huv]
    have e1 : ∑ j, hf L S.Hm (G j) v' * (hf L S.Hm v (w j) + ∑ i, hf L S.Hm (w i) (gs j) * hf L S.Hm v (G i)) =
        ∑ j, hf L S.Hm v (w j) * hf L S.Hm (G j) v' +
          ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * hf L S.Hm (w j) (gs i) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ x, hf L S.Hm v (G x) * (hf L S.Hm (w x) v' + ∑ i, hf L S.Hm (gs x) (w i) * hf L S.Hm (G i) v' +
          ∑ l, hf L S.Hm (G l) v' * hf L S.Hm (w x) (w l)) =
        ∑ x, hf L S.Hm (w x) v' * hf L S.Hm v (G x) +
          ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * (hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (w i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_add, mul_add, mul_comm (hf L S.Hm v (G x)), add_assoc]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have key : (∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * hf L S.Hm (w j) (gs i)) +
        ∑ j, ∑ i, hf L S.Hm v (G j) * hf L S.Hm (G i) v' * (hf L S.Hm (gs j) (w i) + hf L S.Hm (w j) (w i)) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      linear_combination hf L S.Hm v (G j) * hf L S.Hm (G i) v' * K j i
    rw [e1, e2]
    linear_combination key

  have hiso : ∀ x y, hf L S.Hm (m x) (m y) = hf L S.Hm x y := by simp only [hm]; exact iso
  have hmg : ∀ a, m (g a) = g a := fun a => by
    rw [hm, hff]; simp only [haG, hgw, zero_smul, Finset.sum_const_zero, add_zero, sub_zero]
  have hmgs : ∀ j, m (gs j) = gs2 j := fun j => by
    rw [hm, hff]
    simp only [hgsG, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hu, hw]; abel
  have hX : ∀ i, G i ∈ S.spanTo g r := fun i => by
    rw [hG]; exact Submodule.subset_span ⟨i.castSucc, by simp, rfl⟩
  have hfix : ∀ J, ∀ v ∈ S.spanTo g J, m v = v := by
    intro J v hv
    induction hv using Submodule.span_induction with
    | mem y hy => obtain ⟨a, -, rfl⟩ := hy; exact hmg a
    | zero => exact map_zero m
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, ha]
  have hspan : ∀ J v, m v ∈ S.spanTo g J ↔ v ∈ S.spanTo g J := fun J v =>
    ⟨fun h => by
      have e : m (m v) = m v := hfix J _ h
      rw [m.injective e] at h; exact h,
     fun h => by rw [hfix J v h]; exact h⟩
  have hmperp : ∀ v ∈ perp L S.Hm (S.spanTo g r), m v = v - ∑ i, hf L S.Hm v (w i) • G i := by
    intro v hv
    rw [hm, hff]
    simp only [hv _ (hX _), zero_smul, Finset.sum_const_zero, add_zero]
  have hperp : ∀ v, m v ∈ perp L S.Hm (S.spanTo g r) ↔ v ∈ perp L S.Hm (S.spanTo g r) := fun v =>
    ⟨fun h y hy => by
      have := h y hy
      rwa [← hfix r y hy, hiso] at this,
     fun h y hy => by
      rw [← hfix r y hy, hiso]; exact h y hy⟩
  have hpspan : ∀ (f : Fin r → S.V) x,
      x ∈ perp L S.Hm (Submodule.span E (Set.range f)) ↔ ∀ l, hf L S.Hm x (f l) = 0 := fun f x =>
    ⟨fun h l => h _ (Submodule.subset_span ⟨l, rfl⟩),
     fun h => GlobalTheory.FramePsi.hf_span_right L S.Hm x _ (by rintro _ ⟨l, rfl⟩; exact h l)⟩
  refine ⟨m, ?_, hmg, hmgs, ?_⟩
  · simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf]
    refine ⟨⟨hiso, fun j => ⟨fun v => hspan _ v, fun v hv => ?_⟩⟩, hperp, fun v hv => ?_⟩
    · rw [hfix _ v hv, sub_self]; exact Submodule.zero_mem _
    · rw [hmperp v hv, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hX i))
  · intro A hXA hAp
    have hsum : ∀ x, ∑ i, hf L S.Hm x (w i) • G i ∈ A := fun x =>
      hXA _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hX i))
    have hAm : ∀ x, m x ∈ A ↔ x ∈ A := fun x =>
      ⟨fun h => by
        have hp : x ∈ perp L S.Hm (S.spanTo g r) := (hperp x).1 (hAp _ h)
        have e : x = m x + ∑ i, hf L S.Hm x (w i) • G i := by rw [hmperp x hp]; abel
        rw [e]; exact A.add_mem h (hsum x),
       fun h => by rw [hmperp x (hAp x h)]; exact A.sub_mem h (hsum x)⟩
    have hPm : ∀ x, m x ∈ perp L S.Hm (Submodule.span E (Set.range gs2)) ↔
        x ∈ perp L S.Hm (Submodule.span E (Set.range gs)) := fun x => by
      rw [hpspan, hpspan]
      simp only [← hmgs, hiso]
    have hsm : ∀ (Λ : Submodule L.O S.V) x, m x ∈ m • Λ ↔ x ∈ Λ := fun Λ x => by
      rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨fun ⟨y, hy, e⟩ => (m.injective e) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
    ext y
    obtain ⟨x, rfl⟩ := m.surjective y
    rw [hsm]
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, hAm, hPm]
end GlobalTheory.FrameDual
