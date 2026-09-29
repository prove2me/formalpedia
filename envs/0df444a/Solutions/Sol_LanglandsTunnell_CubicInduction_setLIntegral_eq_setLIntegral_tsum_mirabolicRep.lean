-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.setLIntegral_eq_setLIntegral_tsum_mirabolicRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9eba667e-5200-5e7b-92bf-493affe773a8

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_setLIntegral_eq_setLIntegral_tsum_mirabolicRep

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open LanglandsTunnell.CubicInduction

attribute [local instance] NumberField.AdelicHaar.glBorel

open Set
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

namespace UnipotentCosetUnfolding

variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α}
  [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]

private theorem exists_mem_mul_rep {M : Type*} [Group M] {H : Subgroup M}
    (rep : Quotient (QuotientGroup.rightRel H) → M) (hspec : ∀ i, Quotient.mk _ (rep i) = i) (m : M) :
    ∃ u ∈ H, ∃ i, m = u * rep i := by
  refine ⟨m * (rep (Quotient.mk _ m))⁻¹, ?_, Quotient.mk _ m, by simp⟩
  exact QuotientGroup.rightRel_apply.1 (Quotient.exact (hspec (Quotient.mk _ m)))

private theorem eq_of_mul_inv_rep_mem {M : Type*} [Group M] {H : Subgroup M}
    (rep : Quotient (QuotientGroup.rightRel H) → M) (hspec : ∀ i, Quotient.mk _ (rep i) = i)
    {i j : Quotient (QuotientGroup.rightRel H)} (hij : rep i * (rep j)⁻¹ ∈ H) : i = j :=
  calc i = Quotient.mk _ (rep i) := (hspec i).symm
    _ = Quotient.mk _ (rep j) := (Quotient.sound (QuotientGroup.rightRel_apply.2 hij)).symm
    _ = j := hspec j

private theorem existsUnique_rep_mul_mem {M : Type*} [Group M] {H : Subgroup M}
    (rep : Quotient (QuotientGroup.rightRel H) → M) (hspec : ∀ i, Quotient.mk _ (rep i) = i) (m : M) :
    ∃! i, rep i * m ∈ H := by
  obtain ⟨u, hu, i, hi⟩ := exists_mem_mul_rep rep hspec m⁻¹
  have hi' : rep i * m ∈ H := by
    have e : rep i * m = u⁻¹ := by
      rw [eq_inv_mul_of_mul_eq hi.symm, mul_assoc, inv_mul_cancel, mul_one]
    rw [e]
    exact H.inv_mem hu
  refine ⟨i, hi', fun j hj => eq_of_mul_inv_rep_mem rep hspec ?_⟩
  have e : rep j * (rep i)⁻¹ = (rep j * m) * (rep i * m)⁻¹ := by group
  rw [e]
  exact H.mul_mem hj (H.inv_mem hi')

private theorem countable_of_le {Γ N : Subgroup G} [Countable Γ] (hNΓ : N ≤ Γ) : Countable N :=
  (Subgroup.inclusion_injective hNΓ).countable

section GlobalPoints

private theorem globalPoints_injective (F : Type) [Field F] [NumberField F] :
    Function.Injective (globalPoints (𝓞 F) F) := by
  intro γ δ h
  have hinj : Function.Injective (algebraMap F (AdeleRing (𝓞 F) F)) :=
    NumberField.AdeleRing.algebraMap_injective (𝓞 F) F
  ext i j
  apply hinj
  have h' := congrArg (fun u : AdelicGL2 (𝓞 F) F =>
    (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) h
  simpa [globalPoints] using h'

end GlobalPoints

end UnipotentCosetUnfolding

theorem solution
    (DΓ DN : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hDΓ : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range DΓ (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (hDN : IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range DN
      (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) :
    ∀ h : AdelicGL2 (𝓞 ℚ) ℚ → ENNReal, Measurable h →
      (∀ (x : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), h (globalPoints (𝓞 ℚ) ℚ (unipotentGL2 x) * g) = h g) →
      ∫⁻ g in DN, h g ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
        ∫⁻ g in DΓ, ∑' i : MirabolicIndex ℚ, h (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) * g)
          ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  intro h hmeas hinv

  haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) :=
    (Matrix.of (m := Fin 2) (n := Fin 2) (α := ℚ)).symm.injective.countable
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) ℚ) := Units.val_injective.countable
  haveI : Countable (globalPoints (𝓞 ℚ) ℚ).range :=
    (Set.countable_range (globalPoints (𝓞 ℚ) ℚ)).to_subtype
  haveI : Countable (MirabolicIndex ℚ) :=
    inferInstanceAs (Countable (Quotient (QuotientGroup.rightRel (unipotentGL2Hom (R := ℚ)).range)))
  have hle : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range ≤
      (globalPoints (𝓞 ℚ) ℚ).range := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    exact MonoidHom.mem_range.2 ⟨unipotentGL2Hom x, rfl⟩
  haveI : Countable ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range :=
    UnipotentCosetUnfolding.countable_of_le hle

  haveI : SMulInvariantMeasure ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range (AdelicGL2 (𝓞 ℚ) ℚ)
      (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
    ⟨fun n _ hs =>
      SMulInvariantMeasure.measure_preimage_smul (μ := adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) (n : AdelicGL2 (𝓞 ℚ) ℚ) hs⟩

  have hspec : ∀ i : MirabolicIndex ℚ, Quotient.mk _ (mirabolicRep ℚ i) = i :=
    fun i => mirabolicRep_spec (K := ℚ) i

  have hmem : ∀ a : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      globalPoints (𝓞 ℚ) ℚ a ∈ ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range ↔
        a ∈ (unipotentGL2Hom (R := ℚ)).range := by
    intro a
    constructor
    · intro ha
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.1 ha
      exact MonoidHom.mem_range.2 ⟨t, UnipotentCosetUnfolding.globalPoints_injective ℚ ht⟩
    · intro ha
      obtain ⟨t, rfl⟩ := MonoidHom.mem_range.1 ha
      exact MonoidHom.mem_range.2 ⟨t, rfl⟩

  have hrep : ∀ i : MirabolicIndex ℚ, (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i))⁻¹ ∈ (globalPoints (𝓞 ℚ) ℚ).range :=
    fun i => (globalPoints (𝓞 ℚ) ℚ).range.inv_mem (MonoidHom.mem_range.2 ⟨mirabolicRep ℚ i, rfl⟩)
  obtain ⟨R, hR⟩ : ∃ R : MirabolicIndex ℚ → (globalPoints (𝓞 ℚ) ℚ).range,
      ∀ i, (R i : AdelicGL2 (𝓞 ℚ) ℚ) = (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i))⁻¹ :=
    ⟨fun i => ⟨(globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i))⁻¹, hrep i⟩, fun _ => rfl⟩
  have hcoset : ∀ γ : (globalPoints (𝓞 ℚ) ℚ).range, ∃! i : MirabolicIndex ℚ,
      (((R i)⁻¹ * γ : (globalPoints (𝓞 ℚ) ℚ).range) : AdelicGL2 (𝓞 ℚ) ℚ) ∈
        ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range := by
    rintro ⟨γ, hγ⟩
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.1 hγ
    show ∃! i : MirabolicIndex ℚ, (R i : AdelicGL2 (𝓞 ℚ) ℚ)⁻¹ * globalPoints (𝓞 ℚ) ℚ m ∈
      ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range
    simp only [hR, inv_inv, ← map_mul, hmem]
    exact UnipotentCosetUnfolding.existsUnique_rep_mul_mem (mirabolicRep ℚ) hspec m

  have hinv' : ∀ n : ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range,
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, h ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) = h g := by
    rintro ⟨n, hn⟩ g
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.1 hn
    exact hinv t.toAdd g

  have hD₀ := MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
    (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) (globalPoints (𝓞 ℚ) ℚ).range
    ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range hle DΓ hDΓ R hcoset
  have hunfold :=
    (IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives.{0,0,0,0}
      (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) (globalPoints (𝓞 ℚ) ℚ).range
      ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range hle DΓ hDΓ R hcoset).1 h hmeas
  rw [hDN.setLIntegral_eq hD₀ h hinv', hunfold]
  simp only [hR, inv_inv, smul_eq_mul]

end S_LanglandsTunnell_CubicInduction_setLIntegral_eq_setLIntegral_tsum_mirabolicRep
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_setLIntegral_eq_setLIntegral_tsum_mirabolicRep (solution)
