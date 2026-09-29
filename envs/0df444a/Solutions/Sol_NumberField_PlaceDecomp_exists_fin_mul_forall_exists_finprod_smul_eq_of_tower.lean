-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_fin_mul_forall_exists_finprod_smul_eq_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/16f399c3-b676-5b4c-af54-bb44381840d1

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_PlaceDecomp_exists_fin_mul_forall_exists_finprod_smul_eq_of_tower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceDecomp_exists_fin_mul_forall_exists_finprod_smul_eq_of_tower.NumberField"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_fin_mul_forall_exists_finprod_smul_eq_of_tower.NumberField.PlaceDecomp"

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.actRingEquiv_apply PlaceDecomp.smul_def PlaceDecomp.coe_smul_units PlaceDecomp.exists_restrict_decomp_surjective_of_tower PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp actRingEquiv_apply smul_def coe_smul_units exists_restrict_decomp_surjective_of_tower forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace RungSol
p2m_open "NumberField.PlaceDecomp NumberField"

open IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise

section tower
variable (E L F : Type*) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F]

theorem adicCompletionSemialgHom_tower
    (v : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 L)) (hu : u.under (𝓞 E) = v)
    (w : HeightOneSpectrum (𝓞 F)) (hwu : w.under (𝓞 L) = u) (hw : w.under (𝓞 E) = v) (z : v.adicCompletion E) :
    Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) z =
      Extension.adicCompletionSemialgHom L F (⟨w, hwu⟩ : u.Extension (𝓞 F))
        (Extension.adicCompletionSemialgHom E L (⟨u, hu⟩ : v.Extension (𝓞 L)) z) := by
  obtain ⟨z, rfl⟩ := HeightOneSpectrum.adicCompletion.ofCompletion_surjective E v z
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    have hoc : Continuous (HeightOneSpectrum.adicCompletion.ofCompletion :
        (v.valuation E).Completion → v.adicCompletion E) :=
      HeightOneSpectrum.adicCompletion.continuous_ofCompletion E v
    have h1 : Continuous fun z : v.adicCompletion E =>
        Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) z :=
      Extension.adicCompletionSemialgHom_continuous E F _
    have h2 : Continuous fun z : v.adicCompletion E =>
        Extension.adicCompletionSemialgHom L F (⟨w, hwu⟩ : u.Extension (𝓞 F))
          (Extension.adicCompletionSemialgHom E L (⟨u, hu⟩ : v.Extension (𝓞 L)) z) :=
      (Extension.adicCompletionSemialgHom_continuous L F _).comp (Extension.adicCompletionSemialgHom_continuous E L _)
    exact isClosed_eq (h1.comp hoc) (h2.comp hoc)
  | ih x =>
    change Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) (x : v.adicCompletion E) =
      Extension.adicCompletionSemialgHom L F (⟨w, hwu⟩ : u.Extension (𝓞 F))
        (Extension.adicCompletionSemialgHom E L (⟨u, hu⟩ : v.Extension (𝓞 L)) (x : v.adicCompletion E))
    rw [Extension.adicCompletionSemialgHom_coe, Extension.adicCompletionSemialgHom_coe, Extension.adicCompletionSemialgHom_coe]
    congr 1
    simp [← IsScalarTower.algebraMap_apply]
end tower

section action
variable (E L F : Type*) [Field E] [Field L] [Field F] [NumberField F] [Algebra E L] [Algebra L F] [Algebra E F]
  [IsScalarTower E L F]

omit [NumberField F] in
theorem restrictScalars_smul_valuationSubring (σ : F ≃ₐ[L] F) (S : ValuationSubring F) :
    (σ.restrictScalars E) • S = σ • S := by
  ext x
  simp only [ValuationSubring.mem_smul_pointwise_iff_exists]
  rfl

theorem mem_decomp_iff_restrictScalars_mem (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[L] F) :
    σ ∈ NumberField.PlaceDecomp.decomp L F w ↔ σ.restrictScalars E ∈ NumberField.PlaceDecomp.decomp E F w := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, restrictScalars_smul_valuationSubring]

theorem smul_eq_restrictScalars_smul (w : HeightOneSpectrum (𝓞 F)) (σ : NumberField.PlaceDecomp.decomp L F w)
    (z : w.adicCompletion F) :
    σ • z = (⟨(σ : F ≃ₐ[L] F).restrictScalars E, (mem_decomp_iff_restrictScalars_mem E L F w σ).mp σ.2⟩ :
      NumberField.PlaceDecomp.decomp E F w) • z := by
  rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def]
  apply HeightOneSpectrum.adicCompletion.ext
  rw [NumberField.PlaceDecomp.actRingEquiv_apply, NumberField.PlaceDecomp.actRingEquiv_apply]
  rfl
end action

section products
variable {G M : Type*} [Group G] [Finite G] [Field M] [MulSemiringAction G M]

theorem coe_finprod_smul_units (b : Mˣ) [MulDistribMulAction G Mˣ]
    (hcoe : ∀ (g : G) (u : Mˣ), ((g • u : Mˣ) : M) = g • (u : M)) :
    ((∏ᶠ g : G, g • b : Mˣ) : M) = ∏ᶠ g : G, g • (b : M) := by
  rw [show ((∏ᶠ g : G, g • b : Mˣ) : M) = Units.coeHom M (∏ᶠ g : G, g • b) from rfl,
    MonoidHom.map_finprod _ (Set.toFinite _)]
  exact finprod_congr fun g => hcoe g b

theorem smul_finprod_smul_eq (g : G) (y : M) : g • ∏ᶠ h : G, h • y = ∏ᶠ h : G, h • y :=
  smul_finprod_perm y g

end products

end NumberField.PlaceDecomp.RungSol

open NumberField.PlaceDecomp.RungSol _root_.NumberField.PlaceDecomp _root_.P2MW.S_NumberField_PlaceDecomp_exists_fin_mul_forall_exists_finprod_smul_eq_of_tower.NumberField.PlaceDecomp in
theorem solution
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [IsGalois E L] [IsGalois L F]
    (w : HeightOneSpectrum (𝓞 F))
    (h : HeightOneSpectrum.under (𝓞 E) w =
      HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w))
    (n : ℕ) (c : Fin n → ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ)
    (hc : ∀ a : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
      ∃ (i : Fin n) (b : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ),
        (((∏ᶠ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), ρ • b :
            ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) :
            ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : (HeightOneSpectrum.under (𝓞 L) w).adicCompletion L) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom E L
            (⟨HeightOneSpectrum.under (𝓞 L) w, rfl⟩ :
              (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 L))
            ((a * (c i)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) :
              (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E))
    (m : ℕ) (d : Fin m → ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ)
    (hd : ∀ a' : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ,
      ∃ (j : Fin m) (b : (w.adicCompletion F)ˣ),
        (((∏ᶠ τ : ↥(NumberField.PlaceDecomp.decomp L F w), τ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom L F
            (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F))
            ((a' * (d j)⁻¹ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) :
              (HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) :
    ∃ c' : Fin (n * m) → ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
      ∀ a : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
        ∃ (k : Fin (n * m)) (b : (w.adicCompletion F)ˣ),
          (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
              w.adicCompletion F) =
            HeightOneSpectrum.Extension.adicCompletionSemialgHom E F
              (⟨w, h⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 F))
              ((a * (c' k)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) :
                (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E) := by
  classical

  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp L F w) := Fintype.ofFinite _
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)) := Fintype.ofFinite _

  obtain ⟨r, hr_surj, -, hr_ker, -, hr_act⟩ :=
    NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E L F w

  have hcoeF : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (u : (w.adicCompletion F)ˣ), ((g • u : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = g • (u : (w.adicCompletion F)) :=
    fun g u => NumberField.PlaceDecomp.coe_smul_units g u
  have hcoeL : ∀ (g : ↥(NumberField.PlaceDecomp.decomp L F w)) (u : (w.adicCompletion F)ˣ), ((g • u : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = g • (u : (w.adicCompletion F)) :=
    fun g u => NumberField.PlaceDecomp.coe_smul_units g u
  have hcoeLE : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w))) (u : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ), ((g • u : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) = g • (u : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) :=
    fun g u => NumberField.PlaceDecomp.coe_smul_units g u

  have hdesc : ∀ j : Fin m, ∃ e : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
      (HeightOneSpectrum.Extension.adicCompletionSemialgHom E L (⟨HeightOneSpectrum.under (𝓞 L) w, rfl⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 L))) (e : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)) = ∏ᶠ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), ρ • ((d j : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) := by
    intro j
    have hfix : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)),
        σ • (∏ᶠ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), ρ • ((d j : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L))) = ∏ᶠ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), ρ • ((d j : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) :=
      fun σ => smul_finprod_perm _ σ
    obtain ⟨z, hz⟩ := (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom E L
      (HeightOneSpectrum.under (𝓞 L) w) _).mp hfix
    have hy0 : (∏ᶠ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), ρ • ((d j : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L))) ≠ 0 := by
      rw [finprod_eq_prod_of_fintype]
      exact Finset.prod_ne_zero_iff.mpr fun ρ _ => (smul_ne_zero_iff_ne ρ).mpr (d j).ne_zero
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hy0 (by rw [← hz, map_zero])
    exact ⟨Units.mk0 z hz0, hz⟩
  choose e he using hdesc

  refine ⟨fun k => c (finProdFinEquiv.symm k).1 * e (finProdFinEquiv.symm k).2, fun a => ?_⟩
  obtain ⟨i, b₁, hb₁⟩ := hc a
  obtain ⟨j, b₂, hb₂⟩ := hd b₁
  refine ⟨finProdFinEquiv (i, j), b₂, ?_⟩
  simp only [Equiv.symm_apply_apply]

  let ιD : ↥(NumberField.PlaceDecomp.decomp L F w) → ↥(NumberField.PlaceDecomp.decomp E F w) := fun τ =>
    ⟨(τ : F ≃ₐ[L] F).restrictScalars E, (mem_decomp_iff_restrictScalars_mem E L F w τ).mp τ.2⟩
  have hιD_ker : ∀ τ : ↥(NumberField.PlaceDecomp.decomp L F w), r (ιD τ) = 1 := fun τ => (hr_ker _).mpr fun x => (τ : F ≃ₐ[L] F).commutes x
  have hιD_inj : Function.Injective ιD := fun τ₁ τ₂ hτ =>
    Subtype.ext (AlgEquiv.restrictScalars_injective E (congrArg Subtype.val hτ))
  have hιD_surj : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E F w), r σ = 1 → ∃ τ, ιD τ = σ := by
    intro σ hσ
    have hfixL := (hr_ker σ).mp hσ
    let τ : F ≃ₐ[L] F := { (σ : F ≃ₐ[E] F) with commutes' := hfixL }
    have hτE : τ.restrictScalars E = (σ : F ≃ₐ[E] F) := AlgEquiv.ext fun _ => rfl
    have hτ : τ ∈ NumberField.PlaceDecomp.decomp L F w :=
      (mem_decomp_iff_restrictScalars_mem E L F w τ).mpr (hτE ▸ σ.2)
    exact ⟨⟨τ, hτ⟩, Subtype.ext hτE⟩
  have hs : ∀ ρ, r (Function.surjInv hr_surj ρ) = ρ := Function.surjInv_eq hr_surj
  let Θ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)) × ↥(NumberField.PlaceDecomp.decomp L F w) → ↥(NumberField.PlaceDecomp.decomp E F w) := fun p => Function.surjInv hr_surj p.1 * ιD p.2
  have hΘ : Function.Bijective Θ := by
    constructor
    · rintro ⟨ρ₁, τ₁⟩ ⟨ρ₂, τ₂⟩ hpt
      have h1 : ρ₁ = ρ₂ := by
        have := congrArg r hpt
        simpa [Θ, map_mul, hs, hιD_ker] using this
      subst h1
      have h2 : ιD τ₁ = ιD τ₂ := mul_left_cancel hpt
      rw [hιD_inj h2]
    · intro σ
      obtain ⟨τ, hτ⟩ := hιD_surj ((Function.surjInv hr_surj (r σ))⁻¹ * σ)
        (by rw [map_mul, map_inv, hs, inv_mul_cancel])
      exact ⟨(r σ, τ), by simp only [Θ, hτ, mul_inv_cancel_left]⟩

  have hprodL : (∏ τ : ↥(NumberField.PlaceDecomp.decomp L F w), ιD τ • (b₂ : (w.adicCompletion F))) = (HeightOneSpectrum.Extension.adicCompletionSemialgHom L F (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F))) ((b₁ * (d j)⁻¹ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) := by
    rw [← hb₂, coe_finprod_smul_units b₂ hcoeL, finprod_eq_prod_of_fintype]
    exact Finset.prod_congr rfl fun τ _ => (smul_eq_restrictScalars_smul E L F w τ _).symm

  have hb₁' : (∏ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), ρ • (b₁ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L))) = (HeightOneSpectrum.Extension.adicCompletionSemialgHom E L (⟨HeightOneSpectrum.under (𝓞 L) w, rfl⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 L))) ((a * (c i)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)) := by
    rw [← finprod_eq_prod_of_fintype, ← coe_finprod_smul_units b₁ hcoeLE]
    exact hb₁
  have he' : (∏ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), ρ • ((d j : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L))) = (HeightOneSpectrum.Extension.adicCompletionSemialgHom E L (⟨HeightOneSpectrum.under (𝓞 L) w, rfl⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 L))) (e j : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)) := by
    rw [← finprod_eq_prod_of_fintype]
    exact (he j).symm
  have hy_eq : (∏ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), ρ • ((b₁ * (d j)⁻¹ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L))) = (HeightOneSpectrum.Extension.adicCompletionSemialgHom E L (⟨HeightOneSpectrum.under (𝓞 L) w, rfl⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 L))) ((a * (c i * e j)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)) := by
    have hY : ((b₁ * (d j)⁻¹ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) = (b₁ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) * ((d j : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L))⁻¹ := by
      simp [Units.val_mul, Units.val_inv_eq_inv_val]
    rw [hY]
    simp only [smul_mul', smul_inv₀', Finset.prod_mul_distrib, Finset.prod_inv_distrib, hb₁', he']
    rw [← map_inv₀, ← map_mul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]
    ring

  rw [coe_finprod_smul_units b₂ hcoeF, finprod_eq_prod_of_fintype]
  calc ∏ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • (b₂ : (w.adicCompletion F))
      = ∏ p : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)) × ↥(NumberField.PlaceDecomp.decomp L F w), Θ p • (b₂ : (w.adicCompletion F)) :=
        (Fintype.prod_bijective Θ hΘ (fun p => Θ p • (b₂ : (w.adicCompletion F))) (fun σ => σ • (b₂ : (w.adicCompletion F))) (fun _ => rfl)).symm
    _ = ∏ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), Function.surjInv hr_surj ρ • (HeightOneSpectrum.Extension.adicCompletionSemialgHom L F (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F))) ((b₁ * (d j)⁻¹ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) := by
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun ρ _ => ?_
        simp only [Θ, mul_smul]
        rw [← Finset.smul_prod', hprodL]
    _ = ∏ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), (HeightOneSpectrum.Extension.adicCompletionSemialgHom L F (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F))) (ρ • ((b₁ * (d j)⁻¹ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L))) := by
        refine Finset.prod_congr rfl fun ρ _ => ?_
        rw [← hr_act, hs]
    _ = (HeightOneSpectrum.Extension.adicCompletionSemialgHom L F (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F))) (∏ ρ : ↥(NumberField.PlaceDecomp.decomp E L (HeightOneSpectrum.under (𝓞 L) w)), ρ • ((b₁ * (d j)⁻¹ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L))) := (map_prod (HeightOneSpectrum.Extension.adicCompletionSemialgHom L F (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F))) _ _).symm
    _ = (HeightOneSpectrum.Extension.adicCompletionSemialgHom L F (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F))) ((HeightOneSpectrum.Extension.adicCompletionSemialgHom E L (⟨HeightOneSpectrum.under (𝓞 L) w, rfl⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 L))) ((a * (c i * e j)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E))) := by rw [hy_eq]
    _ = (HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, h⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 F))) ((a * (c i * e j)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)) :=
        (adicCompletionSemialgHom_tower E L F _ _ rfl w rfl h _).symm

end S_NumberField_PlaceDecomp_exists_fin_mul_forall_exists_finprod_smul_eq_of_tower
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_fin_mul_forall_exists_finprod_smul_eq_of_tower (solution)
