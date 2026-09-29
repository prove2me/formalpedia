-- Prove2me | solution 1 for NumberField.SUnits.isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/02fd8b35-6428-5099-be7f-7ec29b139953

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationHomDefect
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_GroupCohomology_GlobalBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

namespace B3GB

section generic

variable {k : Type} [CommRing k] {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)

def evD {V W : Rep.{0} k D} (t : (ihom V).obj W) : V →+ W := LinearMap.toAddMonoidHom (show V →ₗ[k] W from t)

lemma evD_d₁₂ {V W : Rep.{0} k D} (φ : D → (ihom V).obj W) (d₁ d₂ : D) (x : V) :
    evD ((d₁₂ ((ihom V).obj W)).hom φ (d₁, d₂)) x =
      W.ρ d₁ (evD (φ d₂) (V.ρ d₁⁻¹ x)) - evD (φ (d₁ * d₂)) x + evD (φ d₁) x := by
  rw [d₁₂_hom_apply]
  rfl

def ev {P : Rep.{0} k D} {A : Rep.{0} k H} (ψ : (ihom (Rep.res π P)).obj A) : P →+ A :=
  LinearMap.toAddMonoidHom (show P →ₗ[k] A from ψ)

lemma cob₂_apply {P : Rep.{0} k D} {A : Rep.{0} k H} (Φ : H → (ihom (Rep.res π P)).obj A) (g₁ g₂ : H) (x : P) :
    ev π ((d₁₂ ((ihom (Rep.res π P)).obj A)).hom Φ (g₁, g₂)) x =
      A.ρ g₁ (ev π (Φ g₂) (P.ρ (π g₁⁻¹) x)) - ev π (Φ (g₁ * g₂)) x + ev π (Φ g₁) x := by
  change ev π (((ihom (Rep.res π P)).obj A).ρ g₁ (Φ g₂) - Φ (g₁ * g₂) + Φ g₁) x = _
  rfl

lemma exists_lift_d₁₂_eq {T : ShortComplex (Rep.{0} k D)} (hT : T.ShortExact) (y : cocycles₁ T.X₃) (c : cocycles₂ T.X₁)
    (hc : (H2π T.X₁).hom c = (δ hT 1 2 rfl).hom ((H1π T.X₃).hom y)) :
    ∃ φ : D → T.X₂, (∀ d, T.g.hom (φ d) = y d) ∧ ∀ dd, (d₁₂ T.X₂).hom φ dd = T.f.hom (c dd) := by

  have hg : Function.Surjective T.g.hom := (Rep.epi_iff_surjective T.g).1 hT.epi_g
  choose φ₀ hφ₀ using fun d => hg (y d)

  have hex := (ShortComplex.moduleCat_exact_iff _).1 (hT.exact.map (forget₂ (Rep k D) (ModuleCat k)))
  have hrange : ∀ dd, ∃ r : T.X₁, T.f.hom r = (d₁₂ T.X₂).hom φ₀ dd := by
    rintro ⟨d₁, d₂⟩
    have h0 := congrFun (cocycles₁.d₁₂_apply y) (d₁, d₂)
    rw [d₁₂_hom_apply] at h0
    refine hex ((d₁₂ T.X₂).hom φ₀ (d₁, d₂)) ?_
    change T.g.hom ((d₁₂ T.X₂).hom φ₀ (d₁, d₂)) = 0
    rw [d₁₂_hom_apply, map_add, map_sub, Rep.hom_comm_apply, hφ₀, hφ₀, hφ₀]
    exact h0
  choose x₀ hx₀ using hrange
  have hδ := δ₁_apply hT y φ₀ (funext hφ₀) x₀ (funext hx₀)
  change (H2π T.X₁).hom c = (δ hT 1 2 rfl) (H1π T.X₃ y) at hc
  rw [hδ] at hc
  change H2π T.X₁ c = H2π T.X₁ _ at hc
  rw [H2π_eq_iff] at hc
  obtain ⟨β, hβ⟩ := hc

  have hrk : LinearMap.range T.f.hom.toLinearMap = LinearMap.ker T.g.hom.toLinearMap :=
    (hT.exact.map (forget₂ (Rep k D) (ModuleCat k))).moduleCat_range_eq_ker
  have hgf : ∀ d, T.g.hom (T.f.hom (β d)) = 0 := fun d => by
    have hmem : T.f.hom.toLinearMap (β d) ∈ LinearMap.ker T.g.hom.toLinearMap := hrk ▸ LinearMap.mem_range_self _ (β d)
    exact LinearMap.mem_ker.1 hmem
  refine ⟨fun d => φ₀ d + T.f.hom (β d), fun d => ?_, fun dd => ?_⟩
  · rw [map_add, hφ₀, hgf, add_zero]
  · obtain ⟨d₁, d₂⟩ := dd
    have hβ' : T.f.hom ((d₁₂ T.X₁).hom β (d₁, d₂)) = T.f.hom (c (d₁, d₂)) - T.f.hom (x₀ (d₁, d₂)) := by
      rw [hβ, Pi.sub_apply, map_sub]
      rfl
    have hnat : (d₁₂ T.X₂).hom (fun d => T.f.hom (β d)) (d₁, d₂) = T.f.hom ((d₁₂ T.X₁).hom β (d₁, d₂)) := by
      rw [d₁₂_hom_apply, d₁₂_hom_apply, map_add, map_sub, Rep.hom_comm_apply]
    change (d₁₂ T.X₂).hom (φ₀ + fun d => T.f.hom (β d)) (d₁, d₂) = _
    rw [map_add, Pi.add_apply, ← hx₀, hnat, hβ', add_sub_cancel]

def toIntLinearMapOfModules {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW ⟨u, u.map_add⟩ (fun c m => by
    letI := instV
    letI := instW
    exact map_intCast_smul u ℤ ℤ c m)

end generic

section units

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
  (ιE : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
  (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))

omit [IsGalois ℚ ↥F] in
include hιE in
lemma coe_toMul_ιE (x : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) :
    ((Additive.toMul (ιE x) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = ((NumberField.SUnits.val ℚ ↥F Sℚ x : (↥F)ˣ) : ↥F) := by
  rw [hιE, Units.coe_map, MonoidHom.coe_coe]
  rfl

include hιE in

lemma ιE_equivariant (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) :
    ιE ((NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ).ρ (AlgEquiv.restrictNormalHom ↥F γ) x) =
      (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (ιE x) := by
  apply Additive.toMul.injective
  apply Units.ext
  rw [coe_toMul_ιE F Sℚ ιE hιE, NumberField.SUnits.val_rho]
  change ((AlgEquiv.restrictNormalHom ↥F γ (NumberField.SUnits.val ℚ ↥F Sℚ x : ↥F) : ↥F) : AlgebraicClosure ℚ) =
    ((γ • Additive.toMul (ιE x) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
  rw [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe, coe_toMul_ιE F Sℚ ιE hιE]
  exact AlgEquiv.restrictNormal_commutes γ ↥F _

omit [IsGalois ℚ ↥F] in
include hιE in

lemma ιE_fixed (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hs : s ∈ F.fixingSubgroup)
    (x : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) :
    (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ s (ιE x) = ιE x := by
  apply Additive.toMul.injective
  apply Units.ext
  change ((s • Additive.toMul (ιE x) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
  rw [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe, coe_toMul_ιE F Sℚ ιE hιE]
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs
  exact (hs _ (NumberField.SUnits.val ℚ ↥F Sℚ x : ↥F).2).trans (coe_toMul_ιE F Sℚ ιE hιE x).symm

end units

end B3GB

set_option maxHeartbeats 3200000 in
open B3GB in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (h1 : (Rep.homSeq₁ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).ShortExact)
    (ιE : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    {ΛE : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) →+ continuousH2S S M}
    (hΛE : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)

    (η : groupCohomology (Rep.defectQ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) 1)
    (c : cocycles₂ ((ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)))
    (hc : (H2π ((ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ))).hom c = (groupCohomology.δ h1 1 2 rfl).hom η)
    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hm : ∀ (γ₁ γ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B), κ b (m (γ₁, γ₂)) =
      ιE (LinearMap.toAddMonoidHom ((c : (↥F ≃ₐ[ℚ] ↥F) × (↥F ≃ₐ[ℚ] ↥F) → (ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) (AlgEquiv.restrictNormalHom ↥F γ₁, AlgEquiv.restrictNormalHom ↥F γ₂)) b))
    (hmS : m ∈ levelCocyclesS₂ S M) :
    ΛE ((groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (Rep.homSeq₂ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).f 1).hom η) = continuousH2Sπ S M ⟨m, hmS⟩ := by
  classical

  revert hc
  refine H1_induction_on (C := fun η' => (H2π ((ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ))).hom c =
      (groupCohomology.δ h1 1 2 rfl).hom η' →
    ΛE ((groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (Rep.homSeq₂ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).f 1).hom η') =
      continuousH2Sπ S M ⟨m, hmS⟩) η ?_
  intro y hc

  obtain ⟨φ, hφy, hφc⟩ := exists_lift_d₁₂_eq (k := ℤ) h1 y c hc

  let a : cocycles₁ ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) :=
    mapCocycles₁ (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (Rep.homSeq₂ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).f y
  have ha : ∀ d, (a : (↥F ≃ₐ[ℚ] ↥F) → _) d = (Rep.homSeq₂ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).f.hom (y d) := fun d => rfl
  have hHa := H1π_comp_map_apply (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (Rep.homSeq₂ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).f y
  let ψ : (↥F ≃ₐ[ℚ] ↥F) → (ihom (Rep.res (AlgEquiv.restrictNormalHom ↥F) (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B))).obj
      (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) :=
    fun d => toIntLinearMapOfModules _ _ (ιE.comp (evD (φ d)))
  have hψ : ∀ (d : ↥F ≃ₐ[ℚ] ↥F) (x : Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B),
      ev (AlgEquiv.restrictNormalHom ↥F) (ψ d) x = ιE (evD (φ d) x) := fun d x => rfl
  have hψf : ∀ (d : ↥F ≃ₐ[ℚ] ↥F) (x : Rep.relationModuleInt B), LinearMap.toAddMonoidHom (ψ d) ((Rep.relationModuleInt.ι B).hom x) =
      ιE (LinearMap.toAddMonoidHom ((a : (↥F ≃ₐ[ℚ] ↥F) → (ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) d) x) := by
    intro d x
    rw [ha, ← hφy d]
    rfl
  have hψlev : ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), F'.IsUnramifiedOutside S ∧
      ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F'.fixingSubgroup →
        ∀ (d : ↥F ≃ₐ[ℚ] ↥F) (x : Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B),
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ s (LinearMap.toAddMonoidHom (ψ d) x) = LinearMap.toAddMonoidHom (ψ d) x :=
    ⟨F, hF, fun s hs d x => ιE_fixed F Sℚ ιE hιE s hs (evD (φ d) x)⟩
  have hφc' : ∀ dd, (d₁₂ ((ihom (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ))).hom φ dd =
      (Rep.preCover B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).hom (c dd) := hφc

  have hm' : ∀ (g₁ g₂ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B),
      κ ((Rep.freeCover B).hom x) (m (g₁, g₂)) =
        LinearMap.toAddMonoidHom ((d₁₂ ((ihom (Rep.res (AlgEquiv.restrictNormalHom ↥F) (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B))).obj
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))).hom (ψ ∘ AlgEquiv.restrictNormalHom ↥F) (g₁, g₂)) x := by
    intro g₁ g₂ x
    rw [hm]
    change _ = ev (AlgEquiv.restrictNormalHom ↥F) ((d₁₂ ((ihom (Rep.res (AlgEquiv.restrictNormalHom ↥F) (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B))).obj
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))).hom (ψ ∘ AlgEquiv.restrictNormalHom ↥F) (g₁, g₂)) x
    rw [cob₂_apply, Function.comp_apply, Function.comp_apply, Function.comp_apply, hψ, hψ, hψ, map_inv, map_mul,
      ← ιE_equivariant F Sℚ ιE hιE]

    have hE : evD (c (AlgEquiv.restrictNormalHom ↥F g₁, AlgEquiv.restrictNormalHom ↥F g₂)) ((Rep.freeCover B).hom x) =
        (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ).ρ (AlgEquiv.restrictNormalHom ↥F g₁)
            (evD (φ (AlgEquiv.restrictNormalHom ↥F g₂)) ((Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) B).ρ (AlgEquiv.restrictNormalHom ↥F g₁)⁻¹ x)) -
          evD (φ (AlgEquiv.restrictNormalHom ↥F g₁ * AlgEquiv.restrictNormalHom ↥F g₂)) x +
          evD (φ (AlgEquiv.restrictNormalHom ↥F g₁)) x := by
      rw [← evD_d₁₂, hφc']
      rfl
    calc ιE (evD (c (AlgEquiv.restrictNormalHom ↥F g₁, AlgEquiv.restrictNormalHom ↥F g₂)) ((Rep.freeCover B).hom x)) = _ :=
          congrArg ιE hE
      _ = _ := by
          rw [map_add, map_sub]
          rfl

  have key := hΛE a ψ hψf hψlev m hm' hmS
  refine Eq.trans ?_ key
  exact congrArg ΛE hHa

end S_NumberField_SUnits_isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta
end P2MW
export P2MW.S_NumberField_SUnits_isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta (solution)
