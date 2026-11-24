-- Prove2me | solution 1 for GlobalTheory.UnitPairNorm.main_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:37.71675+00:00
-- url     : https://prove2.me/submissions/81c0e8a1-a3cf-4264-9917-9a54fae1c69b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
import Theorems.Thm_GlobalTheory_UnitPairNorm_h_add_right
import Theorems.Thm_GlobalTheory_UnitPairNorm_h_smul_right
import Theorems.Thm_GlobalTheory_UnitPairNorm_h_zero_left
import Theorems.Thm_GlobalTheory_UnitPairNorm_exists_unit_pair
import Theorems.Thm_GlobalTheory_UnitPairNorm_exists_unit_norm
import Theorems.Thm_GlobalTheory_UnitPairNorm_exists_norm_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
  [FiniteDimensional E V]
namespace GlobalTheory.UnitPairNorm
theorem _root_.solution (c : E ≃+* E) (hcc : ∀ x, c (c x) = x)
    (hcint : ∀ x : O, ∃ y : O, c (algebraMap O E x) = algebraMap O E y)
    (hnorm : ∀ u : Oˣ, c (algebraMap O E u) = algebraMap O E u →
      ∃ z : Oˣ, algebraMap O E u = algebraMap O E z * c (algebraMap O E z))
    (hz : ∃ z : O, algebraMap O E z + c (algebraMap O E z) = 1)
    (h : V → V → E)
    (hadd : ∀ x y z : V, h (x + y) z = h x z + h y z)
    (hsmul : ∀ (s : E) (x z : V), h (s • x) z = s * h x z)
    (hsym : ∀ x y : V, h y x = c (h x y)) :
    ∀ (n : ℕ) (W : Submodule E V), finrank E W = n → ∀ L : Submodule O V, L.FG →
      Submodule.span E (L : Set V) = W →
      (∀ y ∈ W, (y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap O E).range)) →
      ∃ (m : ℕ) (v : Fin m → V), (∀ i j, h (v i) (v j) = if i = j then 1 else 0) ∧
        Submodule.span O (Set.range v) = L := by
  intro n
  induction n with
  | zero =>
    intro W hW L _ hsp _
    have hW0 : W = ⊥ := Submodule.finrank_eq_zero.mp hW
    have hL : L = ⊥ := by
      rw [eq_bot_iff]; intro x hx
      have : x ∈ W := hsp ▸ Submodule.subset_span hx
      rw [hW0, Submodule.mem_bot] at this
      rw [this]; exact Submodule.zero_mem _
    refine ⟨0, Fin.elim0, fun i => i.elim0, ?_⟩
    rw [hL, Set.range_eq_empty, Submodule.span_empty]
  | succ n ih =>
    intro W hW L hfg hsp hdual
    have hLW : ∀ x ∈ L, x ∈ W := fun x hx => hsp ▸ Submodule.subset_span hx
    have hint : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (algebraMap O E).range :=
      fun x hx y hy => (hdual x (hLW x hx)).mp hx y hy
    have hne : L ≠ ⊥ := by
      rintro rfl
      have : W = ⊥ := by rw [← hsp]; simp
      rw [this, finrank_bot] at hW; omega
    obtain ⟨x, hx, y, hy, a, ha⟩ := exists_unit_pair h hsmul W L hfg hsp hdual hne
    obtain ⟨e0, he0, u, hu⟩ :=
      exists_unit_norm c hcc hcint hz h hadd hsmul hsym L hint x y hx hy a ha
    obtain ⟨e, he, hee⟩ := exists_norm_one c hnorm h hsmul hsym L e0 he0 u hu
    let g : V →ₗ[E] E :=
      { toFun := fun v => h v e
        map_add' := fun v w => hadd v w e
        map_smul' := fun s v => by simp [hsmul] }
    let p : V →ₗ[E] V := LinearMap.id - g.smulRight e
    have hp : ∀ v, p v = v - h v e • e := fun v => rfl
    have hpe : ∀ v, h (p v) e = 0 := by
      intro v; rw [hp, sub_eq_add_neg, ← neg_smul, hadd, hsmul, hee]; ring
    have hpfix : ∀ v, h v e = 0 → p v = v := by
      intro v hv; rw [hp, hv, zero_smul, sub_zero]
    have hpL : ∀ v ∈ L, p v ∈ L := by
      intro v hv
      obtain ⟨o, ho⟩ := hint v hv e he
      rw [hp, ← ho, algebraMap_smul]
      exact L.sub_mem hv (L.smul_mem o he)
    have hpW : ∀ v ∈ W, p v ∈ W := by
      intro v hv; rw [hp]; exact W.sub_mem hv (W.smul_mem _ (hLW e he))
    let W' : Submodule E V := W ⊓ LinearMap.ker g
    let L' : Submodule O V := L.map (p.restrictScalars O)
    have hmemL' : ∀ y, y ∈ L' ↔ y ∈ L ∧ h y e = 0 := by
      intro y
      simp only [L', Submodule.mem_map, LinearMap.coe_restrictScalars]
      constructor
      · rintro ⟨v, hv, rfl⟩; exact ⟨hpL v hv, hpe v⟩
      · rintro ⟨hy, hy0⟩; exact ⟨y, hy, hpfix y hy0⟩
    have hmemW' : ∀ y, y ∈ W' ↔ y ∈ W ∧ h y e = 0 := fun y => Iff.rfl
    have hfg' : L'.FG := hfg.map _
    have hsp' : Submodule.span E (L' : Set V) = W' := by
      apply le_antisymm
      · rw [Submodule.span_le]; intro y hy
        rw [SetLike.mem_coe, hmemL'] at hy
        rw [SetLike.mem_coe, hmemW']; exact ⟨hLW y hy.1, hy.2⟩
      · intro w hw
        rw [hmemW'] at hw
        rw [← hpfix w hw.2]
        have hw1 : w ∈ Submodule.span E (L : Set V) := hsp.symm ▸ hw.1
        have h2 : p w ∈ (Submodule.span E (L : Set V)).map p := Submodule.mem_map_of_mem hw1
        rw [← Submodule.span_image] at h2
        refine Submodule.span_mono ?_ h2
        rintro _ ⟨v, hv, rfl⟩
        exact (hmemL' _).mpr ⟨hpL v hv, hpe v⟩
    have hdual' : ∀ y ∈ W', (y ∈ L' ↔ ∀ z ∈ L', h y z ∈ (algebraMap O E).range) := by
      intro y hy
      rw [hmemW'] at hy
      constructor
      · intro hyL z hz
        exact hint y ((hmemL' y).mp hyL).1 z ((hmemL' z).mp hz).1
      · intro H
        rw [hmemL']
        refine ⟨(hdual y hy.1).mpr ?_, hy.2⟩
        intro x hx
        have hx' : x = p x + h x e • e := by rw [hp, sub_add_cancel]
        have : h y x = h y (p x) := by
          conv_lhs => rw [hx']
          rw [h_add_right c h hadd hsym, h_smul_right c h hsmul hsym, hy.2, mul_zero, add_zero]
        rw [this]
        exact H (p x) ((hmemL' _).mpr ⟨hpL x hx, hpe x⟩)
    have he0 : e ≠ 0 := by
      rintro rfl; rw [h_zero_left h hsmul] at hee; exact zero_ne_one hee
    have hsup : W' ⊔ Submodule.span E {e} = W := by
      apply le_antisymm
      · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr (hLW e he))
      · intro w hw
        have hw' : w = p w + h w e • e := by rw [hp, sub_add_cancel]
        rw [hw']
        exact Submodule.add_mem_sup ((hmemW' _).mpr ⟨hpW w hw, hpe w⟩)
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    have hinf : W' ⊓ Submodule.span E {e} = ⊥ := by
      rw [eq_bot_iff]; intro y hy
      rw [Submodule.mem_inf, hmemW', Submodule.mem_span_singleton] at hy
      obtain ⟨⟨_, hy0⟩, s, rfl⟩ := hy
      rw [hsmul, hee, mul_one] at hy0
      rw [hy0, zero_smul]; exact Submodule.zero_mem _
    have hW' : finrank E W' = n := by
      have := Submodule.finrank_sup_add_finrank_inf_eq W' (Submodule.span E {e})
      rw [hsup, hinf, finrank_bot, finrank_span_singleton he0, hW] at this
      omega
    obtain ⟨m, v', hv'o, hv'sp⟩ := ih W' hW' L' hfg' hsp' hdual'
    have hv'e : ∀ i, h (v' i) e = 0 := fun i =>
      ((hmemL' _).mp (hv'sp ▸ Submodule.subset_span (Set.mem_range_self i))).2
    refine ⟨m + 1, Fin.cons e v', ?_, ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [hee]
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hsym (v' j) e, hv'e, map_zero, if_neg (Fin.succ_ne_zero j).symm]
      · simp [hv'e]
      · simp [hv'o]
    · rw [Fin.range_cons, Submodule.span_insert, hv'sp]
      apply le_antisymm
      · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr he)
          (fun y hy => ((hmemL' y).mp hy).1)
      · intro x hx
        obtain ⟨o, ho⟩ := hint x hx e he
        have hx' : x = p x + o • e := by rw [← algebraMap_smul E o e, ho, hp, sub_add_cancel]
        rw [hx']
        exact Submodule.add_mem _ (Submodule.mem_sup_right ((hmemL' _).mpr ⟨hpL x hx, hpe x⟩))
          (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))
end GlobalTheory.UnitPairNorm
