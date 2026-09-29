-- Prove2me | solution 1 for MvPowerSeries.exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a0d338d2-6e38-5ac0-bee4-7a5b40d28961

import Mathlib
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal

set_option autoImplicit false

open scoped TensorProduct

namespace FreeChartAux

theorem span_range_val {A : Type} [CommRing A] (I : Ideal A) :
    Ideal.span (Set.range (Subtype.val : ↥I → A)) = I := by
  rw [Subtype.range_coe, Ideal.span_eq]

theorem span_range_map_val {B S : Type} [CommRing B] [CommRing S] [Algebra B S]
    (I : Ideal (MvPowerSeries (Fin 2) B)) :
    Ideal.span (Set.range fun i : ↥I =>
        MvPowerSeries.map (algebraMap B S) (i : MvPowerSeries (Fin 2) B)) =
      I.map (MvPowerSeries.map (algebraMap B S)) := by
  show _ = Ideal.span (MvPowerSeries.map (algebraMap B S) '' (I : Set (MvPowerSeries (Fin 2) B)))
  rw [Set.image_eq_range]
  rfl

theorem exists_equiv_baseChange {B : Type} [CommRing B] (I : Ideal (MvPowerSeries (Fin 2) B))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (S : Type) [CommRing S] [Algebra B S] :
    Nonempty (S ⊗[B] (MvPowerSeries (Fin 2) B ⧸ I) ≃ₗ[S]
      (MvPowerSeries (Fin 2) S ⧸ I.map (MvPowerSeries.map (algebraMap B S)))) := by
  set A := MvPowerSeries (Fin 2) B
  have h1 := span_range_val I
  have hN : ∃ q : ℕ, ∀ s : Fin 2, (MvPowerSeries.X s : A) ^ q ∈
      Ideal.span (Set.range (Subtype.val : ↥I → A)) := by
    obtain ⟨q, hq⟩ := hnil
    exact ⟨q, fun s => h1.symm ▸ hq s⟩
  obtain ⟨e, -⟩ := MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem (S := S)
    (Subtype.val : ↥I → A) hN
  let e₀ : (A ⧸ I) ≃ₐ[B] (A ⧸ Ideal.span (Set.range (Subtype.val : ↥I → A))) :=
    Ideal.quotientEquivAlgOfEq B h1.symm
  let e₁ : S ⊗[B] (A ⧸ I) ≃ₗ[S] S ⊗[B] (A ⧸ Ideal.span (Set.range (Subtype.val : ↥I → A))) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) e₀.toLinearEquiv
  let e₂ : (MvPowerSeries (Fin 2) S ⧸
      Ideal.span (Set.range fun i : ↥I => MvPowerSeries.map (algebraMap B S) (i : A))) ≃ₐ[S]
      (MvPowerSeries (Fin 2) S ⧸ I.map (MvPowerSeries.map (algebraMap B S))) :=
    Ideal.quotientEquivAlgOfEq S (span_range_map_val I)
  exact ⟨e₁ ≪≫ₗ e.toLinearEquiv ≪≫ₗ e₂.toLinearEquiv⟩

theorem free_baseChange_of_isUnit {B : Type} [CommRing B] (M : Type) [AddCommGroup M] [Module B M]
    (g : B) [Module.Free (Localization.Away g) (LocalizedModule.Away g M)]
    (R' : Type) [CommRing R'] [Algebra B R'] (hu : IsUnit (algebraMap B R' g)) :
    Module.Free R' (R' ⊗[B] M) := by
  set S := Localization.Away g
  letI : Algebra S R' := (IsLocalization.Away.lift g hu : S →+* R').toAlgebra
  haveI : IsScalarTower B S R' := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply, IsLocalization.Away.lift_comp]

  let ebc : S ⊗[B] M ≃ₗ[S] LocalizedModule.Away g M :=
    (IsLocalizedModule.isBaseChange (.powers g) S (LocalizedModule.mkLinearMap (.powers g) M)).equiv
  haveI : Module.Free S (S ⊗[B] M) := Module.Free.of_equiv ebc.symm

  exact Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange B S R' R' M)

theorem main {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal (MvPowerSeries (Fin 2) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (𝔪 : Ideal B) (h𝔪 : 𝔪.IsMaximal) :
    ∃ g : B, g ∉ 𝔪 ∧ ∀ (R' : Type) [CommRing R'] [Algebra B R'], IsUnit (algebraMap B R' g) →
      Module.Free R' (MvPowerSeries (Fin 2) R' ⧸ I.map (MvPowerSeries.map (algebraMap B R'))) := by
  classical
  set M := MvPowerSeries (Fin 2) B ⧸ I
  haveI := hfin
  haveI := hproj
  haveI : Module.FinitePresentation B M := Module.finitePresentation_of_projective B M
  haveI : 𝔪.IsPrime := h𝔪.isPrime

  have hx : (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum B) ∈ Module.freeLocus B M := by
    rw [Module.freeLocus_eq_univ]; trivial
  haveI : Module.Free (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) := hx

  obtain ⟨g, hg, hgfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    𝔪.primeCompl (LocalizedModule.mkLinearMap 𝔪.primeCompl M) (Localization.AtPrime 𝔪)
  haveI := hgfree
  refine ⟨g, hg, fun R' _ _ hu => ?_⟩
  haveI : Module.Free R' (R' ⊗[B] M) := free_baseChange_of_isUnit M g R' hu
  obtain ⟨e⟩ := exists_equiv_baseChange I hnil R'
  exact Module.Free.of_equiv e

end FreeChartAux

theorem solution
    {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal (MvPowerSeries (Fin 2) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (𝔪 : Ideal B) (h𝔪 : 𝔪.IsMaximal) :
    ∃ g : B, g ∉ 𝔪 ∧ ∀ (R' : Type) [CommRing R'] [Algebra B R'], IsUnit (algebraMap B R' g) →
      Module.Free R' (MvPowerSeries (Fin 2) R' ⧸ I.map (MvPowerSeries.map (algebraMap B R'))) :=
  FreeChartAux.main I hfin hproj hnil 𝔪 h𝔪

end S_MvPowerSeries_exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal
end P2MW
export P2MW.S_MvPowerSeries_exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal (solution)
