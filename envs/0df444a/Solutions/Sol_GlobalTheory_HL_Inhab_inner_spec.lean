-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.inner_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:54:04.923992+00:00
-- url     : https://prove2.me/submissions/2f89a0f6-f416-488b-a5af-bf6e1533594d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_GlobalTheory_HL_Inhab_cj_int
import Theorems.Thm_GlobalTheory_HL_Inhab_hf_sum_left
import Theorems.Thm_GlobalTheory_HL_Inhab_hf_sum_right
import Theorems.Thm_GlobalTheory_HL_Inhab_mem_perp_span
import Theorems.Thm_GlobalTheory_HL_Inhab_spanTo_eq
import Theorems.Thm_GlobalTheory_HL_Inhab_proj_apply
import Theorems.Thm_GlobalTheory_HL_Inhab_mem_innerOf
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Model_hf_add_left
import Theorems.Thm_GlobalTheory_HL_Model_hf_smul_left
import Theorems.Thm_GlobalTheory_HL_Model_hf_smul_right
import Theorems.Thm_GlobalTheory_HL_Model_hf_sub_left
import Theorems.Thm_GlobalTheory_HL_Model_hf_sub_right
import Theorems.Thm_GlobalTheory_HL_Model_hf_symm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (Λ : Submodule L.O S.V)
    (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (hi : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
    (hΛ : IsSD L S.Hm Λ) (hgΛ : ∀ a, g a ∈ Λ) (hsΛ : ∀ j, gs j ∈ Λ)
    (c : E) (hc : c ∈ L.O) (hcz : c * hf L S.Hm (g (Fin.last r)) (g (Fin.last r)) = 1) :
    S.IsInner g gs (innerOf S g gs Λ) ∧ Λ = S.stdLat g gs (innerOf S g gs Λ) := by
  have hsym : ∀ x y, hf L S.Hm y x = L.cj (hf L S.Hm x y) := hf_symm L S.herm.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hΛ.2 y).2 hy x hx
  have hsm : ∀ c ∈ L.O, ∀ x ∈ Λ, c • x ∈ Λ := fun c hc x hx => Λ.smul_mem ⟨c, hc⟩ hx
  have hsg : ∀ a (j : Fin r), hf L S.Hm (gs j) (g a) = if a = j.castSucc then 1 else 0 := by
    intro a j
    rw [hsym, hd]
    split_ifs <;> simp
  have hgg : ∀ i j : Fin r, hf L S.Hm (gs j) (g i.castSucc) = if i = j then 1 else 0 := by
    intro i j
    rw [hsg]
    simp [Fin.castSucc_inj]
  have hA1 : ∀ v (i : Fin r), hf L S.Hm (proj S g gs v) (g i.castSucc) = 0 := by
    intro v i
    simp only [proj_apply, hf_sub_left, hf_sum_left, hf_smul_left, hg, mul_zero,
      Finset.sum_const_zero, sub_zero, hgg, mul_ite, mul_one, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_self]
  have hA2 : ∀ v (i : Fin r), hf L S.Hm (proj S g gs v) (gs i) = 0 := by
    intro v i
    simp only [proj_apply, hf_sub_left, hf_sum_left, hf_smul_left, hi, hd, Fin.castSucc_inj, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, sub_self]
  have hB : ∀ v, v = proj S g gs v + ∑ j, hf L S.Hm v (gs j) • g j.castSucc +
      ∑ j, hf L S.Hm v (g j.castSucc) • gs j := by
    intro v
    rw [proj_apply]
    abel
  have hD : ∀ v, (∀ j : Fin r, hf L S.Hm v (g j.castSucc) = 0) → (∀ j, hf L S.Hm v (gs j) = 0) →
      proj S g gs v = v := by
    intro v h1 h2
    simp [proj_apply, h1, h2]
  have hC : ∀ v ∈ Λ, proj S g gs v ∈ Λ := by
    intro v hv
    rw [proj_apply]
    exact Λ.sub_mem (Λ.sub_mem hv (Λ.sum_mem fun j _ => hsm _ (hint _ hv _ (hsΛ j)) _ (hgΛ _)))
      (Λ.sum_mem fun j _ => hsm _ (hint _ hv _ (hgΛ _)) _ (hsΛ j))
  have hE : ∀ v, proj S g gs (proj S g gs v) = proj S g gs v := fun v => hD _ (hA1 v) (hA2 v)
  have hH : ∀ w, (∀ j : Fin r, hf L S.Hm w (g j.castSucc) = 0) → (∀ j, hf L S.Hm w (gs j) = 0) →
      ∀ y, hf L S.Hm w (proj S g gs y) = hf L S.Hm w y := by
    intro w h1 h2 y
    simp [proj_apply, hf_sub_right, hf_sum_right, hf_smul_right, h1, h2]
  have hH' : ∀ w, (∀ j : Fin r, hf L S.Hm w (g j.castSucc) = 0) → (∀ j, hf L S.Hm w (gs j) = 0) →
      ∀ x, hf L S.Hm (proj S g gs x) w = hf L S.Hm x w := by
    intro w h1 h2 x
    have h1' : ∀ j : Fin r, hf L S.Hm (g j.castSucc) w = 0 := fun j => by rw [hsym, h1, map_zero]
    have h2' : ∀ j, hf L S.Hm (gs j) w = 0 := fun j => by rw [hsym, h2, map_zero]
    simp [proj_apply, hf_sub_left, hf_sum_left, hf_smul_left, h1', h2']
  have hH2 : ∀ x y, (∀ j : Fin r, hf L S.Hm x (g j.castSucc) = 0) →
      (∀ j : Fin r, hf L S.Hm y (g j.castSucc) = 0) → hf L S.Hm (proj S g gs x) y = hf L S.Hm x y := by
    intro x y hx hy
    have hy' : ∀ j : Fin r, hf L S.Hm (g j.castSucc) y = 0 := fun j => by rw [hsym, hy, map_zero]
    simp [proj_apply, hf_sub_left, hf_sum_left, hf_smul_left, hx, hy']
  have hmemA := mem_innerOf S g gs Λ
  have hperpP : ∀ x, x ∈ perp L S.Hm (S.spanTo g r) ↔ ∀ j : Fin r, hf L S.Hm x (g j.castSucc) = 0 := by
    intro x
    simp only [spanTo_eq, mem_perp_span, Set.forall_mem_range]
  have hperpS : ∀ x, x ∈ perp L S.Hm (Submodule.span E (Set.range gs)) ↔
      ∀ j, hf L S.Hm x (gs j) = 0 := by
    intro x
    simp only [mem_perp_span, Set.forall_mem_range]
  have hprojA : ∀ z ∈ Λ, proj S g gs z ∈ innerOf S g gs Λ := fun z hz =>
    (hmemA _).2 ⟨hA1 z, by rw [hE]; exact hC z hz⟩
  have hPA : ∀ x ∈ S.spanTo g r,
      (∀ j : Fin r, hf L S.Hm x (g j.castSucc) = 0) ∧ proj S g gs x = 0 := by
    intro x hx
    rw [spanTo_eq] at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      refine ⟨fun j => hg _ j, ?_⟩
      simp only [proj_apply, hd, Fin.castSucc_inj, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, hg, Finset.sum_const_zero, sub_self]
    | zero => exact ⟨fun j => by simp [hf], map_zero _⟩
    | add u v _ _ hu hv =>
      exact ⟨fun j => by rw [hf_add_left, hu.1, hv.1, add_zero], by rw [map_add, hu.2, hv.2, add_zero]⟩
    | smul c u _ hu =>
      exact ⟨fun j => by rw [hf_smul_left, hu.1, mul_zero], by rw [map_smul, hu.2, smul_zero]⟩
  have hlast : g (Fin.last r) ∈ innerOf S g gs Λ := (hmemA _).2 ⟨fun j => hg _ j, hC _ (hgΛ _)⟩
  have hIs : S.IsInner g gs (innerOf S g gs Λ) := by
    refine ⟨fun x hx => (hmemA x).2 ⟨(hPA x hx).1, by rw [(hPA x hx).2]; exact Λ.zero_mem⟩,
      fun x hx => (hperpP x).2 ((hmemA x).1 hx).1, ?_, ?_, hlast, ?_⟩
    · have heq : innerOf S g gs Λ ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O =
          Λ.map ((proj S g gs).restrictScalars L.O) := by
        ext x
        simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map,
          LinearMap.coe_restrictScalars]
        constructor
        · rintro ⟨hxA, hxS⟩
          have h1 := (hmemA x).1 hxA
          have hpx : proj S g gs x = x := hD x h1.1 ((hperpS x).1 hxS)
          exact ⟨x, by rw [← hpx]; exact h1.2, hpx⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨hprojA y hy, (hperpS _).2 (hA2 y)⟩
      rw [heq]
      exact hΛ.1.1.map _
    · intro y hy
      have hyg := (hperpP y).1 hy
      simp only [Frames.h]
      constructor
      · intro h
        refine (hmemA y).2 ⟨hyg, (hΛ.2 _).1 fun z hz => ?_⟩
        rw [← hH' _ (hA1 y) (hA2 y) z, hH _ (hA1 z) (hA2 z)]
        exact h _ (hprojA z hz)
      · intro hyA x hxA
        have hx := (hmemA x).1 hxA
        rw [← hH2 x y hx.1 hyg, ← hH _ (hA1 x) (hA2 x)]
        exact hint _ hx.2 _ ((hmemA y).1 hyA).2
    · refine ⟨L.cj c • g (Fin.last r), (innerOf S g gs Λ).smul_mem ⟨L.cj c, cj_int L hc⟩ hlast, ?_⟩
      simp only [Frames.h]
      rw [hf_smul_right, L.cj_cj, hcz]
  refine ⟨hIs, ?_⟩
  unfold Frames.stdLat
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [hB z]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_inf.2
        ⟨hprojA z hz, (Submodule.restrictScalars_mem _ _ _).2 ((hperpS _).2 (hA2 z))⟩))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ (⟨_, hint _ hz _ (hsΛ j)⟩ : L.O) (Submodule.subset_span ⟨j, rfl⟩)))
    · exact Submodule.mem_sup_right (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ (⟨_, hint _ hz _ (hgΛ _)⟩ : L.O) (Submodule.subset_span ⟨j, rfl⟩))
  · refine sup_le (sup_le ?_ ?_) ?_
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hgΛ _
    · intro x hx
      rw [Submodule.mem_inf, Submodule.restrictScalars_mem] at hx
      have h1 := (hmemA x).1 hx.1
      rw [← hD x h1.1 ((hperpS x).1 hx.2)]
      exact h1.2
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hsΛ j
end GlobalTheory.HL.Inhab
