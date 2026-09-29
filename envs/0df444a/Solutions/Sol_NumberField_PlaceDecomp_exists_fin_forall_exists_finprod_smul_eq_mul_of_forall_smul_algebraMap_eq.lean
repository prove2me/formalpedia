-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ea10b3bf-d26f-5114-8e65-32d350bb0398

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_adicCompletionSemialgHom_comp_of_tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory IsDedekindDomain NumberField P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq.NumberField"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq.NumberField.PlaceDecomp Pointwise"

namespace NumberField
p2m_export "NumberField" "PlaceDecomp.decomp PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp actRingEquiv_apply smul_def coe_smul_units forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace TransferSol
p2m_open "NumberField.PlaceDecomp NumberField"

set_option linter.unusedSectionVars false

variable {E L F : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
  [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F]
  (w : HeightOneSpectrum (𝓞 F))

theorem restrictScalars_mem (τ : ↥(decomp L F w)) :
    AlgEquiv.restrictScalars E (τ : F ≃ₐ[L] F) ∈ decomp E F w := by
  have h1 := τ.2
  rw [MulAction.mem_stabilizer_iff] at h1 ⊢
  rw [← SetLike.coe_set_eq, ValuationSubring.coe_pointwise_smul] at h1 ⊢
  convert h1 using 1
  all_goals try rfl

theorem ofRingEquiv_mem (σ : ↥(decomp E F w))
    (hfix : ∀ x : L, (σ : F ≃ₐ[E] F) (algebraMap L F x) = algebraMap L F x) :
    AlgEquiv.ofRingEquiv (f := ((σ : F ≃ₐ[E] F) : F ≃+* F)) hfix ∈ decomp L F w := by
  have h1 := σ.2
  rw [MulAction.mem_stabilizer_iff] at h1 ⊢
  rw [← SetLike.coe_set_eq, ValuationSubring.coe_pointwise_smul] at h1 ⊢
  convert h1 using 1
  all_goals try rfl

theorem smul_eq_smul_of_coe_eq (σ : ↥(decomp E F w)) (τ : ↥(decomp L F w))
    (hστ : ((σ : F ≃ₐ[E] F) : F ≃+* F) = ((τ : F ≃ₐ[L] F) : F ≃+* F)) (y : w.adicCompletion F) :
    σ • y = τ • y := by
  rw [smul_def, smul_def]
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  rw [actRingEquiv_apply, actRingEquiv_apply, hστ]

end NumberField.PlaceDecomp.TransferSol

open _root_.NumberField.PlaceDecomp _root_.P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq.NumberField.PlaceDecomp NumberField.PlaceDecomp.TransferSol in
theorem solution
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [IsGalois L F]
    (w : HeightOneSpectrum (𝓞 F))
    (h : HeightOneSpectrum.under (𝓞 E) w =
      HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w))
    (hfix : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : L),
      (σ : F ≃ₐ[E] F) (algebraMap L F x) = algebraMap L F x)
    (m : ℕ) (d : Fin m → ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ)
    (hd : ∀ a' : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ,
      ∃ (j : Fin m) (b : (w.adicCompletion F)ˣ),
        (((∏ᶠ τ : ↥(NumberField.PlaceDecomp.decomp L F w), τ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom L F
            (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F))
            ((a' * (d j)⁻¹ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) :
              (HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) :
    ∃ c : Fin m → ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
      ∀ a : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
        ∃ (k : Fin m) (b : (w.adicCompletion F)ˣ),
          (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
              w.adicCompletion F) =
            HeightOneSpectrum.Extension.adicCompletionSemialgHom E F
              (⟨w, h⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 F))
              ((a * (c k)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) :
                (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E) := by
  classical

  set iL := HeightOneSpectrum.Extension.adicCompletionSemialgHom L F
      (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F)) with hiL
  set iE := HeightOneSpectrum.Extension.adicCompletionSemialgHom E F
      (⟨w, h⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 F)) with hiE
  set iEL := HeightOneSpectrum.Extension.adicCompletionSemialgHom E L
      (⟨HeightOneSpectrum.under (𝓞 L) w, rfl⟩ :
        (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 L)) with hiEL

  have htower : ∀ x, iL (iEL x) = iE x :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionSemialgHom_comp_of_tower E L F w h

  let toL : ↥(decomp E F w) → ↥(decomp L F w) := fun σ =>
    ⟨AlgEquiv.ofRingEquiv (f := ((σ : F ≃ₐ[E] F) : F ≃+* F)) (hfix σ), ofRingEquiv_mem w σ (hfix σ)⟩
  let toE : ↥(decomp L F w) → ↥(decomp E F w) := fun τ =>
    ⟨AlgEquiv.restrictScalars E (τ : F ≃ₐ[L] F), restrictScalars_mem w τ⟩
  have hsmulL : ∀ (σ : ↥(decomp E F w)) (y : w.adicCompletion F), σ • y = toL σ • y := fun σ y =>
    smul_eq_smul_of_coe_eq w σ (toL σ) (by ext x; rfl) y
  have hsmulE : ∀ (τ : ↥(decomp L F w)) (y : w.adicCompletion F), toE τ • y = τ • y := fun τ y =>
    smul_eq_smul_of_coe_eq w (toE τ) τ (by ext x; rfl) y
  have hbij : Function.Bijective toL := by
    refine Function.bijective_iff_has_inverse.2 ⟨toE, fun σ => ?_, fun τ => ?_⟩
    · apply Subtype.ext; apply AlgEquiv.ext; intro x; rfl
    · apply Subtype.ext; apply AlgEquiv.ext; intro x; rfl
  have hfixed : ∀ y : w.adicCompletion F,
      (∀ σ : ↥(decomp E F w), σ • y = y) ↔ (∀ τ : ↥(decomp L F w), τ • y = y) := by
    intro y
    constructor
    · intro hy τ; rw [← hsmulE]; exact hy _
    · intro hy σ; rw [hsmulL]; exact hy _

  have aux : ∀ (u : HeightOneSpectrum (𝓞 E)) (hu : HeightOneSpectrum.under (𝓞 E) w = u) (y : w.adicCompletion F),
      (∀ σ : ↥(decomp E F w), σ • y = y) ↔
        y ∈ Set.range (HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hu⟩ : u.Extension (𝓞 F))) := by
    intro u hu y
    subst hu
    exact NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom E F w y
  have hrangeE : ∀ y : w.adicCompletion F, (∀ σ : ↥(decomp E F w), σ • y = y) ↔ y ∈ Set.range iE :=
    fun y => aux _ h y
  have hrangeL : ∀ y : w.adicCompletion F, (∀ τ : ↥(decomp L F w), τ • y = y) ↔ y ∈ Set.range iL :=
    fun y => NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom L F w y

  have hdj : ∀ j : Fin m, ∃ x : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E,
      iE x = iL (d j : (HeightOneSpectrum.under (𝓞 L) w).adicCompletion L) := by
    intro j
    have h1 : iL (d j : (HeightOneSpectrum.under (𝓞 L) w).adicCompletion L) ∈ Set.range iL := ⟨_, rfl⟩
    rw [← hrangeL, ← hfixed, hrangeE] at h1
    obtain ⟨x, hx⟩ := h1
    exact ⟨x, hx⟩
  choose c₀ hc₀ using hdj
  have hc₀ne : ∀ j, c₀ j ≠ 0 := by
    intro j hj
    have := hc₀ j
    rw [hj, map_zero] at this
    exact (d j).ne_zero ((map_eq_zero iL).1 this.symm)
  refine ⟨fun j => Units.mk0 (c₀ j) (hc₀ne j), fun a => ?_⟩

  have ha' : iEL (a : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E) ≠ 0 :=
    (map_ne_zero iEL).2 a.ne_zero
  obtain ⟨j, b, hb⟩ := hd (Units.mk0 _ ha')
  refine ⟨j, b, ?_⟩
  have hprod : (∏ᶠ σ : ↥(decomp E F w), σ • b) = ∏ᶠ τ : ↥(decomp L F w), τ • b := by
    refine finprod_eq_of_bijective toL hbij fun σ => ?_
    apply Units.ext
    rw [coe_smul_units, coe_smul_units]
    exact hsmulL σ _
  rw [hprod, hb]
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0,
    map_mul, map_inv₀, map_mul, map_inv₀, htower, hc₀]

end S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq (solution)
