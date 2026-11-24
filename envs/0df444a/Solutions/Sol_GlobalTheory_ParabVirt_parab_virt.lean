-- Prove2me | solution 1 for GlobalTheory.ParabVirt.parab_virt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:54:45.633706+00:00
-- url     : https://prove2.me/submissions/293499d7-8f54-4f54-973f-4c205cf3988b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParabolicInductionTrivialPreservesVirtualCharact
import Theorems.Thm_GlobalTheory_ParabVirt_sum_fibres
import Theorems.Thm_GlobalTheory_ParabVirt_lin_surjective
import Theorems.Thm_GlobalTheory_ParabVirt_map_eq_map_iff
import Theorems.Thm_GlobalTheory_ParabVirt_conj_mem_stab_iff
import Theorems.Thm_GlobalTheory_BI_virt_mul_comap_conj_ind_linear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.ParabVirt
variable {F : Type} [Field F] {n : ℕ}
open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
private theorem exists_gl_map_lin_eq_of_finrank_eq (W₀ W : Submodule F (Fin n → F))
    (h : Module.finrank F W₀ = Module.finrank F W) :
    ∃ t : GL (Fin n) F, W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap = W := by
  obtain ⟨C₀, hC₀⟩ := Submodule.exists_isCompl W₀
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have h₁ := Submodule.finrank_add_eq_of_isCompl hC₀
  have h₂ := Submodule.finrank_add_eq_of_isCompl hC
  let E : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    (W₀.prodEquivOfIsCompl C₀ hC₀).symm ≪≫ₗ
      (LinearEquiv.prodCongr (LinearEquiv.ofFinrankEq W₀ W h)
        (LinearEquiv.ofFinrankEq C₀ C (by omega))) ≪≫ₗ W.prodEquivOfIsCompl C hC
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.ParabVirt.lin_surjective E
  refine ⟨t, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hs : (W₀.prodEquivOfIsCompl C₀ hC₀).symm v = (⟨v, hv⟩, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left W₀ C₀ hC₀ ⟨v, hv⟩
    simp [ht, E, hs]
  · rw [LinearEquiv.finrank_map_eq, h]
end GlobalTheory.ParabVirt
end
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.ParabVirt
variable {F : Type} [Field F] {n : ℕ}
open Polynomial
variable {F : Type} [Field F] {n : ℕ}
namespace GlobalTheory.ParabVirt
namespace _root_.GlobalTheory.ParabVirt
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ a n : ℕ, (fun x : GL (Fin a) F => Φ (Fin a → F) (Matrix.toLin' (x : Matrix (Fin a) (Fin a) F))) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin a) F) → (fun x : GL (Fin n) F => ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a ∧ ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W}, Φ W.1 ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict W.2.2)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin n) F) := by
  intro F _ _ Φ hΦ a n hχ
  classical
  have hG := _root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear (GL (Fin n) F)
  have hGa := _root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear (GL (Fin a) F)
  by_cases ha : a ≤ n
  swap
  · convert (_root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin n) F)).zero_mem using 1
    funext x
    rw [Pi.zero_apply]
    haveI : IsEmpty {W : Submodule F (Fin n → F) // Module.finrank F W = a ∧
        ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W} :=
      ⟨fun W => ha (by
        have h₁ := Submodule.finrank_le W.1
        rw [Module.finrank_fin_fun, W.2.1] at h₁
        exact h₁)⟩
    exact finsum_of_isEmpty _
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Submodule F (Fin n → F), Module.finrank F W₀ = a := by
    refine ⟨Submodule.span F (Set.range fun i : Fin a => (Pi.single (Fin.castLE ha i) (1 : F) :
      Fin n → F)), ?_⟩
    rw [finrank_span_eq_card, Fintype.card_fin]
    convert (Pi.basisFun F (Fin n)).linearIndependent.comp _ (Fin.castLE_injective ha) using 1
    ext i : 1
    simp
  let e₀ : W₀ ≃ₗ[F] (Fin a → F) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hW₀, Module.finrank_fin_fun])
  let P := _root_.GlobalTheory.ParabVirt.stab W₀
  let ρ : P →* GL (Fin a) F := (_root_.GlobalTheory.ParabVirt.resMat W₀ e₀).toHomUnits
  let χ : GL (Fin a) F → ℂ := fun y => Φ (Fin a → F) (Matrix.toLin' (y : Matrix (Fin a) (Fin a) F))
  have hψ : (fun p : P => χ (ρ p)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ P := hGa.2.1 χ hχ P ρ
  convert hG.2.2.2.1 P _ hψ using 1
  funext x
  have hval : ∀ p : P, χ (ρ p) =
      Φ W₀ ((Matrix.toLin' ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).restrict p.2) := by
    intro p
    simp only [χ, ρ, MonoidHom.coe_toHomUnits]
    exact (congrArg (Φ (Fin a → F)) (Matrix.toLin'_toMatrix' (e₀.conj
      ((Matrix.toLin' ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).restrict p.2)))).trans
      (hΦ _ _ e₀ _)
  haveI : Fintype (Submodule F (Fin n → F)) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  let π : GL (Fin n) F → {W : Submodule F (Fin n → F) // Module.finrank F W = a} := fun t =>
    ⟨W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap, by
      rw [LinearEquiv.finrank_map_eq, hW₀]⟩
  let f : {W : Submodule F (Fin n → F) // Module.finrank F W = a} → ℂ := fun W =>
    if h : ∀ v ∈ W.1, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W.1 then
      Φ W.1 ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict h) else 0
  let p : {W : Submodule F (Fin n → F) // Module.finrank F W = a} → Prop := fun W =>
    ∀ v ∈ W.1, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W.1
  have hs : Function.Surjective π := fun W => by
    obtain ⟨t, ht⟩ := exists_gl_map_lin_eq_of_finrank_eq W₀ W.1 (by rw [hW₀, W.2])
    exact ⟨t, Subtype.ext ht⟩
  have hπ : ∀ s t, π s = π t ↔ s⁻¹ * t ∈ P := fun s t =>
    Subtype.ext_iff.trans (_root_.GlobalTheory.ParabVirt.map_eq_map_iff W₀ s t)
  have hpt : ∀ t, _root_.GlobalTheory.BI.ext0 P (fun p => χ (ρ p)) (t⁻¹ * x * t) = f (π t) := by
    intro t
    unfold _root_.GlobalTheory.BI.ext0
    by_cases h : t⁻¹ * x * t ∈ P
    · have h' : ∀ v ∈ W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap,
          Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈
            W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap :=
        (_root_.GlobalTheory.ParabVirt.conj_mem_stab_iff W₀ x t).1 h
      rw [dif_pos h]
      show χ (ρ ⟨_, h⟩) = _
      rw [hval]
      simp only [f, π]
      rw [dif_pos h']
      symm
      refine (congrArg (Φ ↥(W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap)) ?_).trans
        (hΦ _ _ ((_root_.GlobalTheory.ParabVirt.lin t).submoduleMap W₀) _)
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      obtain ⟨w, rfl⟩ := ((_root_.GlobalTheory.ParabVirt.lin t).submoduleMap W₀).surjective u
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
      simp only [LinearMap.restrict_coe_apply, LinearEquiv.submoduleMap_apply, Subgroup.coe_mk,
        ← _root_.GlobalTheory.ParabVirt.lin_apply]
      change _ = _root_.GlobalTheory.ParabVirt.lin t
        (_root_.GlobalTheory.ParabVirt.lin (t⁻¹ * x * t) (w : Fin n → F))
      simp only [← _root_.GlobalTheory.ParabVirt.lin_mul, Subgroup.coe_mk, mul_assoc,
        mul_inv_cancel_left]
    · have h' : ¬ ∀ v ∈ W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap,
          Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈
            W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap :=
        fun h' => h ((_root_.GlobalTheory.ParabVirt.conj_mem_stab_iff W₀ x t).2 h')
      rw [dif_neg h]
      simp only [f, π]
      rw [dif_neg h']
  unfold _root_.GlobalTheory.BI.ind
  rw [finsum_congr hpt, finsum_eq_sum_of_fintype (fun t => f (π t)), _root_.GlobalTheory.ParabVirt.sum_fibres P π hs hπ f,
    ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), one_mul,
    finsum_eq_sum_of_fintype,
    ← Fintype.sum_subtype_add_sum_subtype p f]
  have hzero : ∑ W : {W // ¬ p W}, f W = 0 := Finset.sum_eq_zero (fun W _ => dif_neg W.2)
  rw [hzero, add_zero]
  exact (Fintype.sum_equiv (Equiv.subtypeSubtypeEquivSubtypeInter _ _) _ _
    (fun W => dif_pos W.2)).symm
end _root_.GlobalTheory.ParabVirt
end GlobalTheory.ParabVirt
